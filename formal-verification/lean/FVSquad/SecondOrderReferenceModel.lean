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
| `sorm_euler_dt_zero_pos` | ✅ | dt=0 → position unchanged (identity step) |
| `sorm_euler_dt_zero_rate` | ✅ | dt=0 → rate unchanged (identity step) |
| `sorm_euler_restoring_formula` | ✅ | When rate=rs=0: new_rate = kx·dt·(ss−pos) |
| `sorm_euler_correction_neg` | ✅ | pos > ss, kx>0, dt>0, rate=0 → new_rate < 0 (spring pulls back) |
| `sorm_euler_correction_pos` | ✅ | pos < ss, kx>0, dt>0, rate=0 → new_rate > 0 (spring pushes forward) |
| `sorm_euler_new_rate_mono_ss` | ✅ | kx·dt ≥ 0 → new_rate monotone in setpoint ss |
| `sorm_euler_new_pos_mono_rate` | ✅ | dt ≥ 0 → new_pos monotone in rate |

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

/-! ## Additional theorems: identity step, restoring force, monotonicity -/

namespace PX4.SecondOrderReferenceModel

/-- When the time step is zero, the position does not change. -/
theorem sorm_euler_dt_zero_pos (st : SormState) (kx kv ss rs : Rat) :
    (sormEulerStep st kx kv 0 ss rs).pos = st.pos := by
  unfold sormEulerStep; rw [Rat.zero_mul, Rat.add_zero]

/-- When the time step is zero, the rate does not change. -/
theorem sorm_euler_dt_zero_rate (st : SormState) (kx kv ss rs : Rat) :
    (sormEulerStep st kx kv 0 ss rs).rate = st.rate := by
  unfold sormEulerStep
  simp only [Rat.mul_zero, Rat.zero_mul, Rat.zero_add, Rat.add_zero]
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.one_mul]

/-- **Restoring force formula**: when filter_rate = 0 and rate_sample = 0,
    the new rate equals `kx·dt·(ss − pos)` — the proportional corrective acceleration.

    This is the central control-theory property of the SORM: the model applies a
    "spring force" proportional to position error (spring constant = Kx).
    Note that the damping term vanishes (since rate = 0), giving a clean expression. -/
theorem sorm_euler_restoring_formula (kx kv dt ss : Rat)
    (st : SormState) (hrate : st.rate = 0) :
    (sormEulerStep st kx kv dt ss 0).rate = kx * dt * (ss - st.pos) := by
  unfold sormEulerStep; rw [hrate]
  simp only [Rat.mul_zero, Rat.add_zero]
  rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_comm]
  congr 1; simp only [Rat.neg_mul, Rat.mul_neg]

private theorem sub_neg_of_lt (ss pos : Rat) (h : ss < pos) : ss - pos < 0 := by
  rw [Rat.sub_eq_add_neg]
  have key : ss + (-pos) < pos + (-pos) := (Rat.add_lt_add_right).mpr h
  rwa [Rat.add_neg_cancel] at key

private theorem pos_sub_of_lt (pos ss : Rat) (h : pos < ss) : 0 < ss - pos := by
  rw [Rat.sub_eq_add_neg]
  have key : pos + (-pos) < ss + (-pos) := (Rat.add_lt_add_right).mpr h
  rwa [Rat.add_neg_cancel] at key

/-- **Corrective restoring force (negative)**: when the filter position is above the setpoint
    and the rate is zero, the first Euler step produces a negative rate correction.
    Requires `kx > 0` (positive spring constant) and `dt > 0` (positive time step). -/
theorem sorm_euler_correction_neg (kx kv dt ss : Rat)
    (st : SormState) (hrate : st.rate = 0)
    (hkx : 0 < kx) (hdt : 0 < dt) (hpos : ss < st.pos) :
    (sormEulerStep st kx kv dt ss 0).rate < 0 := by
  rw [sorm_euler_restoring_formula kx kv dt ss st hrate]
  have hkxdt : 0 < kx * dt := Rat.mul_pos hkx hdt
  rw [Rat.mul_comm]
  exact (Rat.mul_neg_iff_of_pos_right hkxdt).mpr (sub_neg_of_lt ss st.pos hpos)

/-- **Corrective restoring force (positive)**: when the filter position is below the setpoint
    and the rate is zero, the first Euler step produces a positive rate correction. -/
theorem sorm_euler_correction_pos (kx kv dt ss : Rat)
    (st : SormState) (hrate : st.rate = 0)
    (hkx : 0 < kx) (hdt : 0 < dt) (hpos : st.pos < ss) :
    0 < (sormEulerStep st kx kv dt ss 0).rate := by
  rw [sorm_euler_restoring_formula kx kv dt ss st hrate]
  exact Rat.mul_pos (Rat.mul_pos hkx hdt) (pos_sub_of_lt st.pos ss hpos)

/-- **Monotonicity in setpoint**: a larger position setpoint produces a larger (or equal)
    new rate, whenever `kx·dt ≥ 0`.  Reflects that raising the target adds positive
    corrective acceleration. -/
theorem sorm_euler_new_rate_mono_ss
    (st : SormState) (kx kv dt ss1 ss2 rs : Rat)
    (hkxdt : 0 ≤ kx * dt) (hss : ss1 ≤ ss2) :
    (sormEulerStep st kx kv dt ss1 rs).rate ≤ (sormEulerStep st kx kv dt ss2 rs).rate := by
  simp only [sormEulerStep]
  apply (Rat.add_le_add_right).mpr
  apply (Rat.add_le_add_left).mpr
  exact Rat.mul_le_mul_of_nonneg_left hss hkxdt

/-- **Monotonicity in rate**: a larger filter rate produces a larger (or equal) new
    position after one Euler step, whenever `dt ≥ 0`.  Confirms that positive rate
    moves the state forward along the position axis. -/
theorem sorm_euler_new_pos_mono_rate
    (st1 st2 : SormState) (kx kv dt ss rs : Rat)
    (hpos : st1.pos = st2.pos) (hdt : 0 ≤ dt) (hrate : st1.rate ≤ st2.rate) :
    (sormEulerStep st1 kx kv dt ss rs).pos ≤ (sormEulerStep st2 kx kv dt ss rs).pos := by
  simp only [sormEulerStep, hpos]
  apply (Rat.add_le_add_left).mpr
  exact Rat.mul_le_mul_of_nonneg_left hrate hdt

end PX4.SecondOrderReferenceModel
