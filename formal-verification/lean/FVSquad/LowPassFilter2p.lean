/-!
# PX4 LowPassFilter2p — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `LowPassFilter2p<T>::apply`
from PX4-Autopilot's `mathlib`, a second-order Butterworth IIR low-pass filter.

- **C++ source**: `src/lib/mathlib/math/filter/LowPassFilter2p.hpp`

## C++ reference (Direct Form II)

```cpp
inline T apply(const T &sample) {
    T delay_element_0 = sample - _delay_element_1 * _a1 - _delay_element_2 * _a2;
    T output          = delay_element_0 * _b0 + _delay_element_1 * _b1 + _delay_element_2 * _b2;
    _delay_element_2  = _delay_element_1;
    _delay_element_1  = delay_element_0;
    return output;
}
```

State: `(_delay_element_1, _delay_element_2)` — two delay (memory) elements.
Coefficients: `(b0, b1, b2, a1, a2)`.  For the second-order Butterworth design:
- `b1 = 2 * b0`, `b2 = b0`  (symmetric numerator)
- DC gain = `(b0+b1+b2) / (1+a1+a2)` = 1 when `b0+b1+b2 = 1+a1+a2`

The `disable()` state sets `b0=1, b1=0, b2=0, a1=0, a2=0` — pure pass-through.

## Model

Over `Rat` (rational arithmetic, exact). Coefficients are taken as explicit
parameters; the Butterworth coefficient computation (`tanf`, `cosf`) is out of scope.

## Key properties proved

| Theorem | Status | Description |
|---------|--------|-------------|
| `lpf2p_disabled_passthrough` | ✅ | Disabled coefficients → output = input |
| `lpf2p_butterworth_b1` | ✅ | Butterworth: b1 = 2*b0 |
| `lpf2p_butterworth_b2` | ✅ | Butterworth: b2 = b0 |
| `lpf2p_apply_linear` | ✅ | Apply is linear in (sample, d1, d2) |
| `lpf2p_zero_state_zero_input` | ✅ | Zero state + zero input → zero output |
| `lpf2p_delay_update_d1` | ✅ | New d1 = w0 = sample - d1*a1 - d2*a2 |
| `lpf2p_delay_update_d2` | ✅ | New d2 = old d1 |
| `lpf2p_butterworth_output_sym` | ✅ | Output = b0 * (w0 + 2*d1 + d2) for Butterworth |
| `lpf2p_dc_gain_one` | ✅ | DC steady-state: d1=d2=w_ss → output = x |
| `lpf2p_butterworth_dc_balance` | ✅ | DC balance cond. simplifies to 4*b0=1+a1+a2 |
| `lpf2p_disabled_two_steps` | ✅ | Two-step disabled filter passes input through |
| `lpf2p_ss_w_intermediate` | ✅ | At steady state, intermediate w0 = w_ss |
| `lpf2p_dc_ss_output` | ✅ | DC output formula: y_ss = w_ss*(b0+b1+b2) |

## Approximations / out of scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Coefficient computation** (`set_cutoff_frequency`): involves `tanf`, `cosf`; out of scope.
- **BIBO stability**: requires `|z-plane poles| < 1`; only structural properties proved here.
-/

namespace PX4.LowPassFilter2p

/-! ## Private arithmetic helpers (no Mathlib ring/linarith available) -/

private theorem rat_mul_sub (a b c : Rat) : a * (b - c) = a * b - a * c := by
  rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, ← Rat.sub_eq_add_neg]

/-- Cancellation: `w + x + y + (-x) + (-y) = w`. -/
private theorem rat_cancel3 (w x y : Rat) : w + x + y + -x + -y = w := by
  rw [Rat.add_assoc (w + x + y)]
  rw [show -x + -y = -(x + y) from Rat.neg_add.symm]
  rw [show w + x + y = w + (x + y) from Rat.add_assoc w x y]
  rw [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

/-- `b + 2*b + b = 4*b`. -/
private theorem rat_4mul (b : Rat) : b + 2 * b + b = 4 * b := by
  have h2 : (2 : Rat) * b = b + b := by
    rw [show (2 : Rat) = 1 + 1 from by native_decide, Rat.add_mul, Rat.one_mul]
  have h4 : (4 : Rat) * b = b + b + b + b := by
    rw [show (4 : Rat) = 1 + 1 + 1 + 1 from by native_decide,
        Rat.add_mul, Rat.add_mul, Rat.add_mul, Rat.one_mul]
  rw [h2, h4, Rat.add_comm b (b + b)]

/-! ## State and coefficient types -/

structure LPF2pState where
  d1 : Rat  -- _delay_element_1
  d2 : Rat  -- _delay_element_2
  deriving Repr, DecidableEq

structure LPF2pCoeffs where
  b0 : Rat
  b1 : Rat
  b2 : Rat
  a1 : Rat
  a2 : Rat
  deriving Repr

/-- The `disable()` coefficient set: pure pass-through. -/
def disabledCoeffs : LPF2pCoeffs := { b0 := 1, b1 := 0, b2 := 0, a1 := 0, a2 := 0 }

/-- Zero-initialised state. -/
def zeroState : LPF2pState := { d1 := 0, d2 := 0 }

/-! ## The core `apply` function (Direct Form II) -/

/-- Models `LowPassFilter2p<T>::apply`. Returns `(new_state, output)`. -/
def lpf2pApply (c : LPF2pCoeffs) (s : LPF2pState) (sample : Rat) :
    LPF2pState × Rat :=
  let w0  := sample - s.d1 * c.a1 - s.d2 * c.a2
  let out := w0 * c.b0 + s.d1 * c.b1 + s.d2 * c.b2
  ({ d1 := w0, d2 := s.d1 }, out)

/-! ## Theorem 1: disabled coefficients give pass-through -/

/-- When the filter is disabled (`b0=1, b1=b2=a1=a2=0`), `apply sample = sample`. -/
theorem lpf2p_disabled_passthrough (s : LPF2pState) (x : Rat) :
    (lpf2pApply disabledCoeffs s x).2 = x := by
  simp [lpf2pApply, disabledCoeffs,
        Rat.mul_zero, Rat.zero_mul, Rat.mul_one, Rat.sub_eq_add_neg,
        Rat.neg_zero, Rat.add_zero, Rat.zero_add]

/-! ## Theorem 2: Butterworth numerator symmetry -/

/-- Butterworth design constraint: `b1 = 2 * b0` and `b2 = b0`. -/
def isButterworth (c : LPF2pCoeffs) : Prop :=
  c.b1 = 2 * c.b0 ∧ c.b2 = c.b0

/-- For Butterworth coefficients, `b1 = 2 * b0`. -/
theorem lpf2p_butterworth_b1 (c : LPF2pCoeffs) (h : isButterworth c) : c.b1 = 2 * c.b0 := h.1

/-- For Butterworth coefficients, `b2 = b0`. -/
theorem lpf2p_butterworth_b2 (c : LPF2pCoeffs) (h : isButterworth c) : c.b2 = c.b0 := h.2

/-! ## Theorem 3: Output linearity -/

/-- `apply` is linear: scaling input and both delay elements by `k` scales output by `k`. -/
theorem lpf2p_apply_linear (c : LPF2pCoeffs) (s : LPF2pState) (x k : Rat) :
    let s' := { d1 := k * s.d1, d2 := k * s.d2 }
    (lpf2pApply c s' (k * x)).2 = k * (lpf2pApply c s x).2 := by
  simp only [lpf2pApply]
  -- Goal: (k*x - k*d1*a1 - k*d2*a2)*b0 + k*d1*b1 + k*d2*b2 = k*((x - d1*a1 - d2*a2)*b0 + d1*b1 + d2*b2)
  have hfact : k * x - k * s.d1 * c.a1 - k * s.d2 * c.a2
             = k * (x - s.d1 * c.a1 - s.d2 * c.a2) := by
    rw [rat_mul_sub, rat_mul_sub, ← Rat.mul_assoc k s.d1, ← Rat.mul_assoc k s.d2]
  rw [hfact, Rat.mul_add, Rat.mul_add,
      ← Rat.mul_assoc k, ← Rat.mul_assoc k s.d1, ← Rat.mul_assoc k s.d2]

/-! ## Theorem 4: Zero state + zero input → zero output -/

/-- Starting from `zeroState`, applying `sample = 0` gives output `0` and leaves
    state at zero. -/
theorem lpf2p_zero_state_zero_input (c : LPF2pCoeffs) :
    lpf2pApply c zeroState 0 = (zeroState, 0) := by
  simp [lpf2pApply, zeroState, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.zero_mul]

/-! ## Theorems 5–6: Delay element update correctness -/

/-- After `apply`, the new `d1` equals `w0 = sample - d1*a1 - d2*a2`. -/
theorem lpf2p_delay_update_d1 (c : LPF2pCoeffs) (s : LPF2pState) (x : Rat) :
    (lpf2pApply c s x).1.d1 = x - s.d1 * c.a1 - s.d2 * c.a2 := by
  simp [lpf2pApply]

/-- After `apply`, the new `d2` equals the old `d1`. -/
theorem lpf2p_delay_update_d2 (c : LPF2pCoeffs) (s : LPF2pState) (x : Rat) :
    (lpf2pApply c s x).1.d2 = s.d1 := by
  simp [lpf2pApply]

/-! ## Theorem 7: Butterworth symmetric output formula -/

/-- For Butterworth coefficients (`b1 = 2*b0`, `b2 = b0`), the output equals
    `b0 * (w0 + 2 * d1 + d2)` — exposing the symmetric FIR structure. -/
theorem lpf2p_butterworth_output_sym (c : LPF2pCoeffs) (s : LPF2pState) (x : Rat)
    (hb : isButterworth c) :
    let w0 := x - s.d1 * c.a1 - s.d2 * c.a2
    (lpf2pApply c s x).2 = c.b0 * (w0 + 2 * s.d1 + s.d2) := by
  obtain ⟨hb1, hb2⟩ := hb
  simp only [lpf2pApply, hb1, hb2]
  -- goal: w0*b0 + d1*(2*b0) + d2*b0 = b0*(w0 + 2*d1 + d2)
  simp only [Rat.mul_add, Rat.mul_comm, Rat.mul_assoc]
  rw [show s.d1 * (c.b0 * 2) = c.b0 * (s.d1 * 2) by
    rw [← Rat.mul_assoc s.d1 c.b0, Rat.mul_comm s.d1 c.b0, Rat.mul_assoc c.b0 s.d1]]

/-! ## Theorem 8: DC steady-state output = x -/

/-
   At DC steady state with constant input `x`:
   - w_ss = x / (1 + a1 + a2)   (from w_ss = x - a1*w_ss - a2*w_ss)
   - d1 = d2 = w_ss
   - output = w_ss * (b0+b1+b2) = x * (b0+b1+b2)/(1+a1+a2)
   - Unit DC gain when b0+b1+b2 = 1+a1+a2: output = x

   Here we prove: if d1=d2=w_ss where w_ss*(1+a1+a2) = x, then output = x*(b0+b1+b2)/(1+a1+a2).
   For the unit-DC-gain case (b0+b1+b2 = 1+a1+a2) the output equals x.
-/

/-- At DC steady state with delay elements at `w_ss = x/(1+a1+a2)`,
    the intermediate value is also `w_ss`. -/
theorem lpf2p_ss_w_intermediate (c : LPF2pCoeffs) (x w_ss : Rat)
    (hss : w_ss * (1 + c.a1 + c.a2) = x) :
    let s := { d1 := w_ss, d2 := w_ss }
    (lpf2pApply c s x).1.d1 = w_ss := by
  simp only [lpf2pApply]
  have expand : w_ss * (1 + c.a1 + c.a2) = w_ss + w_ss * c.a1 + w_ss * c.a2 := by
    rw [Rat.mul_add, Rat.mul_add, Rat.mul_one]
  rw [← hss, expand, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  exact rat_cancel3 w_ss (w_ss * c.a1) (w_ss * c.a2)

/-- At DC steady state, the output equals `w_ss * (b0+b1+b2)`. -/
theorem lpf2p_dc_ss_output (c : LPF2pCoeffs) (x w_ss : Rat)
    (hss : w_ss * (1 + c.a1 + c.a2) = x) :
    let s := { d1 := w_ss, d2 := w_ss }
    (lpf2pApply c s x).2 = w_ss * (c.b0 + c.b1 + c.b2) := by
  simp only [lpf2pApply]
  have expand : w_ss * (1 + c.a1 + c.a2) = w_ss + w_ss * c.a1 + w_ss * c.a2 := by
    rw [Rat.mul_add, Rat.mul_add, Rat.mul_one]
  have hw : x - w_ss * c.a1 - w_ss * c.a2 = w_ss := by
    rw [← hss, expand, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
    exact rat_cancel3 w_ss (w_ss * c.a1) (w_ss * c.a2)
  rw [hw, Rat.mul_add, Rat.mul_add]

/-- DC gain = 1: if DC balance holds (`b0+b1+b2 = 1+a1+a2`) and the delay elements
    are at DC steady state (`d1 = d2 = w_ss` where `w_ss*(1+a1+a2) = x`), then output = x. -/
theorem lpf2p_dc_gain_one (c : LPF2pCoeffs) (x w_ss : Rat)
    (hss  : w_ss * (1 + c.a1 + c.a2) = x)
    (hbal : c.b0 + c.b1 + c.b2 = 1 + c.a1 + c.a2) :
    let s := { d1 := w_ss, d2 := w_ss }
    (lpf2pApply c s x).2 = x := by
  simp only []
  have h := lpf2p_dc_ss_output c x w_ss hss
  simp only [] at h
  rw [h, hbal]
  exact hss

/-! ## Theorem 9: Butterworth DC balance condition -/

/-- For Butterworth coefficients (`b1 = 2*b0`, `b2 = b0`), the DC balance condition
    `b0 + b1 + b2 = 1 + a1 + a2` simplifies to `4 * b0 = 1 + a1 + a2`. -/
theorem lpf2p_butterworth_dc_balance (c : LPF2pCoeffs) (hb : isButterworth c) :
    (c.b0 + c.b1 + c.b2 = 1 + c.a1 + c.a2) ↔ (4 * c.b0 = 1 + c.a1 + c.a2) := by
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · intro h
    rw [hb1, hb2] at h
    rw [rat_4mul] at h
    exact h
  · intro h
    rw [hb1, hb2, rat_4mul]
    exact h

/-! ## Theorem 10: Two-step disabled filter -/

/-- Two consecutive applications of the disabled filter both pass input through. -/
theorem lpf2p_disabled_two_steps (x : Rat) :
    let s0 := zeroState
    let (s1, o1) := lpf2pApply disabledCoeffs s0 x
    let (_s2, o2) := lpf2pApply disabledCoeffs s1 x
    o1 = x ∧ o2 = x := by
  simp [lpf2pApply, disabledCoeffs, zeroState,
        Rat.mul_zero, Rat.zero_mul, Rat.mul_one, Rat.sub_eq_add_neg,
        Rat.neg_zero, Rat.add_zero, Rat.zero_add]

/-! ## Numerical examples -/

/-- Example: disabled filter with state (1/2, 1/4) passes input 3 unchanged. -/
example : (lpf2pApply disabledCoeffs { d1 := 1/2, d2 := 1/4 } 3).2 = 3 := by
  native_decide

/-- Example: zero state with disabled filter, two steps both give x. -/
example (x : Rat) : (lpf2pApply disabledCoeffs zeroState x).2 = x := by
  simp [lpf2pApply, disabledCoeffs, zeroState,
        Rat.mul_zero, Rat.zero_mul, Rat.mul_one, Rat.sub_eq_add_neg,
        Rat.neg_zero, Rat.add_zero, Rat.zero_add]

end PX4.LowPassFilter2p
