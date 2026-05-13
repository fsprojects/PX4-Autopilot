/-!
# PX4 SecondOrderReferenceModel (Forward-Euler) — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of the forward-Euler
state transition in `math::SecondOrderReferenceModel<T>` from PX4-Autopilot.

- **C++ source**: `src/lib/mathlib/math/filter/second_order_reference_model.hpp`

## C++ reference (Forward-Euler update)

```
// Ad = I + Ac * T,  Bd = Bc * T
// state_matrix:
//   (0,0) = 1,          (0,1) = T
//   (1,0) = -Kx * T,    (1,1) = 1 - Kv * T
// input_matrix:
//   (0,0) = 0,           (0,1) = 0
//   (1,0) = Kx * T,      (1,1) = Kv * T
//
// new_state = filter_state + T * filter_rate
// new_rate  = (-Kx*T)*filter_state + (1-Kv*T)*filter_rate
//           + (Kx*T)*state_sample + (Kv*T)*rate_sample
```

State: `(filter_state, filter_rate)`.
Parameters: `Kx` (spring constant = natural_freq^2), `Kv` (damping coefficient = 2*zeta*natural_freq), `T` (time step).

## Model

Over `Rat` (exact rational arithmetic). Parameters `Kx`, `Kv`, `T` are
taken as free rational parameters.

## Key properties proved

| Theorem | Status | Description |
|---------|--------|-------------|
| `sorm_reset_state` | ✅ | After reset, filter_state = s |
| `sorm_reset_rate` | ✅ | After reset, filter_rate = r |
| `sorm_euler_new_state` | ✅ | Forward-Euler new state = old_state + T * old_rate |
| `sorm_euler_new_rate` | ✅ | Forward-Euler new rate formula |
| `sorm_euler_equilibrium_state` | ✅ | At equilibrium (fs=ss, fr=rs=0), new_state = ss |
| `sorm_euler_equilibrium_rate` | ✅ | At equilibrium, new_rate = 0 |
| `sorm_euler_zero_rate_state` | ✅ | Zero rate + at-target: state unchanged |

## Approximations / out of scope

- IEEE 754 float semantics: NaN, infinity, and rounding not modelled.
- Parameter computation (`setParameters`): involves transcendental functions; out of scope.
- Max time step guard: the C++ code resets when `time_step > max_time_step`; not modelled.
- Bilinear discretization method: only Forward-Euler is modelled here.
- Vector T: model only scalar T = Rat; vector case is componentwise.
-/

namespace PX4.SecondOrderReferenceModel

/-! ## State type -/

/-- A forward-Euler SORM state: position and rate. -/
structure SormState where
  pos : Rat
  rate : Rat
  deriving Repr, DecidableEq

/-! ## Reset -/

/-- Reset the filter to a given state and rate. -/
def sormReset (s r : Rat) : SormState :=
  { pos := s, rate := r }

/-! ## Forward-Euler step -/

/-- One forward-Euler integration step.
    - `st` : current filter state (pos, rate)
    - `kx` : spring constant  (Kx = natural_freq^2)
    - `kv` : damping coefficient (Kv = 2*zeta*natural_freq)
    - `dt` : time step T
    - `ss` : state (position) setpoint sample
    - `rs` : rate setpoint sample (often 0)
-/
def sormEulerStep (st : SormState) (kx kv dt ss rs : Rat) : SormState :=
  let newPos  := st.pos + dt * st.rate
  let newRate := -kx * dt * st.pos + (1 - kv * dt) * st.rate
              +  kx * dt * ss     +  kv * dt * rs
  { pos := newPos, rate := newRate }

/-! ## Theorems -/

/-! ### Reset theorems -/

/-- After reset, the position component equals the supplied state. -/
theorem sorm_reset_state (s r : Rat) : (sormReset s r).pos = s := rfl

/-- After reset, the rate component equals the supplied rate. -/
theorem sorm_reset_rate (s r : Rat) : (sormReset s r).rate = r := rfl

/-! ### Forward-Euler update theorems -/

/-- The new position after a forward-Euler step equals `old_pos + dt * old_rate`. -/
theorem sorm_euler_new_state (st : SormState) (kx kv dt ss rs : Rat) :
    (sormEulerStep st kx kv dt ss rs).pos = st.pos + dt * st.rate := rfl

/-- The new rate after a forward-Euler step follows the discrete state equation:
    `new_rate = -Kx*T*pos + (1 - Kv*T)*rate + Kx*T*ss + Kv*T*rs`. -/
theorem sorm_euler_new_rate (st : SormState) (kx kv dt ss rs : Rat) :
    (sormEulerStep st kx kv dt ss rs).rate =
      -kx * dt * st.pos + (1 - kv * dt) * st.rate + kx * dt * ss + kv * dt * rs := rfl

/-- At equilibrium (filter_pos = setpoint, filter_rate = 0, rate_setpoint = 0),
    the new position remains unchanged at the setpoint. -/
theorem sorm_euler_equilibrium_state (ss kx kv dt : Rat)
    (st : SormState) (hpos : st.pos = ss) (hrate : st.rate = 0) :
    (sormEulerStep st kx kv dt ss 0).pos = ss := by
  simp only [sormEulerStep, hpos, hrate, Rat.mul_zero, Rat.add_zero]

/-- At equilibrium (filter_pos = setpoint, filter_rate = 0, rate_setpoint = 0),
    the new rate is 0 — the equilibrium is a fixed point of the Euler update. -/
theorem sorm_euler_equilibrium_rate (ss kx kv dt : Rat)
    (st : SormState) (hpos : st.pos = ss) (hrate : st.rate = 0) :
    (sormEulerStep st kx kv dt ss 0).rate = 0 := by
  simp only [sormEulerStep, hpos, hrate]
  -- After substitution: -kx*dt*ss + (1-kv*dt)*0 + kx*dt*ss + kv*dt*0 = 0
  rw [Rat.mul_zero, Rat.mul_zero, Rat.add_zero, Rat.add_zero]
  -- Goal: -kx * dt * ss + kx * dt * ss = 0
  have : -kx * dt * ss = -(kx * dt * ss) := by
    rw [Rat.neg_mul, Rat.neg_mul]
  rw [this]
  exact Rat.neg_add_cancel (kx * dt * ss)

/-- When the filter is at the target position with zero rate,
    the state (position) does not change in one Euler step. -/
theorem sorm_euler_zero_rate_state (ss kx kv dt : Rat)
    (st : SormState) (hpos : st.pos = ss) (hrate : st.rate = 0) :
    (sormEulerStep st kx kv dt ss 0).pos = st.pos := by
  simp only [sormEulerStep, hrate, Rat.mul_zero, Rat.add_zero, hpos]

end PX4.SecondOrderReferenceModel
