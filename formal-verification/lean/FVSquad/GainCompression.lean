/-!
# PX4 GainCompression — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `GainCompression::update`
from PX4-Autopilot's rate control library.

- **C++ source**: `src/lib/rate_control/gain_compression.cpp`
- **C++ header**: `src/lib/rate_control/gain_compression.hpp`

## C++ reference

```cpp
float GainCompression::update(const float input, const float dt) {
  _hpf = _alpha_hpf * _hpf + _alpha_hpf * (input - _input_prev);
  _lpf.update(_hpf * _hpf);
  _input_prev = input;
  const float ka = fmaxf(_compression_gain - _compression_gain_min, 0.f);
  const float spectral_damping = -_kSpectralDamperGain * ka * _lpf.getState();
  const float leakage = _kLeakageGain * (1.f - _compression_gain);
  const float ka_dot = spectral_damping + leakage;
  _compression_gain = math::constrain(
    _compression_gain + ka_dot * dt, _compression_gain_min, 1.f);
  return _compression_gain;
}
```

## Key property

The central safety property: **compression_gain always stays in [gain_min, 1]** after
every call to `update`, regardless of the input signal or timestep.  This follows
directly from `math::constrain(_, gain_min, 1.f)`.

## Approximations / out of scope

- **Float arithmetic**: `Rat` models exact arithmetic; no overflow, NaN, ±∞.
- **Filter internals**: HPF/LPF state are not modelled; `ka_dot` is left abstract.
-/

namespace PX4.GainCompression

/-! ## Rational constrain -/

/-- `constrainRat val lo hi` clamps `val` to the interval `[lo, hi]`.
    Models `math::constrain` over rational numbers. -/
def constrainRat (val lo hi : Rat) : Rat :=
  if val < lo then lo
  else if val > hi then hi
  else val

/-- `constrainRat` always returns a value ≥ lo (given lo ≤ hi). -/
theorem constrainRat_ge_lo (val lo hi : Rat) (h : lo ≤ hi) :
    lo ≤ constrainRat val lo hi := by
  simp only [constrainRat]
  by_cases h1 : val < lo
  · -- val < lo: result = lo, need lo ≤ lo
    simp only [if_pos h1]
    exact Rat.le_refl
  · -- ¬(val < lo): result = if val > hi then hi else val
    simp only [if_neg h1]
    by_cases h2 : val > hi
    · -- val > hi: result = hi, need lo ≤ hi (hypothesis h)
      simp only [if_pos h2]
      exact h
    · -- ¬(val > hi): result = val, need lo ≤ val (from ¬(val < lo))
      simp only [if_neg h2]
      exact Rat.not_lt.mp h1

/-- `constrainRat` always returns a value ≤ hi (given lo ≤ hi). -/
theorem constrainRat_le_hi (val lo hi : Rat) (h : lo ≤ hi) :
    constrainRat val lo hi ≤ hi := by
  simp only [constrainRat]
  by_cases h1 : val < lo
  · -- val < lo: result = lo, need lo ≤ hi (hypothesis h)
    simp only [if_pos h1]
    exact h
  · -- ¬(val < lo): result = if val > hi then hi else val
    simp only [if_neg h1]
    by_cases h2 : val > hi
    · -- val > hi: result = hi, need hi ≤ hi
      simp only [if_pos h2]
      exact Rat.le_refl
    · -- ¬(val > hi): result = val, need val ≤ hi (from ¬(val > hi))
      simp only [if_neg h2]
      exact Rat.not_lt.mp h2

/-- `constrainRat` returns a value in `[lo, hi]`. -/
theorem constrainRat_in_range (val lo hi : Rat) (h : lo ≤ hi) :
    lo ≤ constrainRat val lo hi ∧ constrainRat val lo hi ≤ hi :=
  ⟨constrainRat_ge_lo val lo hi h, constrainRat_le_hi val lo hi h⟩

/-- If `val` is already in `[lo, hi]`, `constrainRat` is the identity. -/
theorem constrainRat_of_mem (val lo hi : Rat) (hlo : lo ≤ val) (hhi : val ≤ hi) :
    constrainRat val lo hi = val := by
  simp only [constrainRat]
  by_cases h1 : val < lo
  · exact absurd h1 (Rat.not_lt.mpr hlo)
  · simp only [if_neg h1]
    by_cases h2 : val > hi
    · exact absurd h2 (Rat.not_lt.mpr hhi)
    · simp only [if_neg h2]

/-- Idempotence: applying `constrainRat` twice gives the same result as once. -/
theorem constrainRat_idempotent (val lo hi : Rat) (h : lo ≤ hi) :
    constrainRat (constrainRat val lo hi) lo hi = constrainRat val lo hi :=
  constrainRat_of_mem _ lo hi
    (constrainRat_ge_lo val lo hi h)
    (constrainRat_le_hi val lo hi h)

/-! ## GainCompression update model -/

/-- Abstract model of one `GainCompression::update` step.

    Parameters:
    - `gain`:     current compression gain
    - `ka_dot`:   computed rate-of-change (spectral_damping + leakage), arbitrary
    - `dt`:       timestep, arbitrary
    - `gain_min`: minimum allowed compression gain

    Returns the new compression gain after clamping to `[gain_min, 1]`. -/
def gainCompressionUpdate (gain ka_dot dt gain_min : Rat) : Rat :=
  constrainRat (gain + ka_dot * dt) gain_min 1

/-! ## Key invariant: range containment -/

/-- **Range invariant**: `gainCompressionUpdate` always returns a value in
    `[gain_min, 1]`, provided `gain_min ≤ 1`.

    This is the central safety property of `GainCompression::update`: the final
    `math::constrain` call guarantees the output is always in [gain_min, 1],
    regardless of the HPF/LPF state or input signal. -/
theorem gainCompressionUpdate_in_range (gain ka_dot dt gain_min : Rat)
    (hm : gain_min ≤ 1) :
    gain_min ≤ gainCompressionUpdate gain ka_dot dt gain_min ∧
    gainCompressionUpdate gain ka_dot dt gain_min ≤ 1 :=
  constrainRat_in_range (gain + ka_dot * dt) gain_min 1 hm

/-- **Lower bound**: the result is always ≥ `gain_min`. -/
theorem gainCompressionUpdate_ge_min (gain ka_dot dt gain_min : Rat)
    (hm : gain_min ≤ 1) :
    gain_min ≤ gainCompressionUpdate gain ka_dot dt gain_min :=
  (gainCompressionUpdate_in_range gain ka_dot dt gain_min hm).1

/-- **Upper bound**: the result is always ≤ 1. -/
theorem gainCompressionUpdate_le_one (gain ka_dot dt gain_min : Rat)
    (hm : gain_min ≤ 1) :
    gainCompressionUpdate gain ka_dot dt gain_min ≤ 1 :=
  (gainCompressionUpdate_in_range gain ka_dot dt gain_min hm).2

/-- **Iterated range invariant**: after any number of updates, the compression gain
    stays in `[gain_min, 1]`, regardless of the sequence of `(ka_dot, dt)` pairs. -/
theorem gainCompressionIterate_in_range
    (gain gain_min : Rat)
    (hg0 : gain_min ≤ gain) (hg1 : gain ≤ 1) (hm : gain_min ≤ 1)
    (steps : List (Rat × Rat)) :
    let final_gain := steps.foldl
      (fun g step => gainCompressionUpdate g step.1 step.2 gain_min) gain
    gain_min ≤ final_gain ∧ final_gain ≤ 1 := by
  induction steps generalizing gain with
  | nil => exact ⟨hg0, hg1⟩
  | cons step rest ih =>
    simp only [List.foldl]
    exact ih _
      (gainCompressionUpdate_ge_min gain step.1 step.2 gain_min hm)
      (gainCompressionUpdate_le_one gain step.1 step.2 gain_min hm)

/-! ## Leakage toward 1 -/

/-- **Leakage drives gain toward 1**: when `gain < 1`, the leakage term is positive.
    In C++: `leakage = _kLeakageGain * (1 - _compression_gain)`. -/
theorem gainCompression_leakage_positive (gain kLeakage : Rat)
    (hg : gain < 1) (hk : 0 < kLeakage) :
    0 < kLeakage * (1 - gain) := by
  apply Rat.mul_pos hk
  exact (Rat.lt_iff_sub_pos gain 1).mp hg

/-- **At gain = 1, leakage is zero**. -/
theorem gainCompression_leakage_at_max (kLeakage : Rat) :
    kLeakage * (1 - 1) = 0 := by
  simp [Rat.sub_self]

/-! ## Concrete examples -/

-- Update with positive ka_dot (gain increase)
#eval gainCompressionUpdate (3/10) (1/5) (1/100) (3/10)   -- 151/500 ≈ 0.302
-- Update with large negative ka_dot (gain decrease)
#eval gainCompressionUpdate 1 (-50) (1/100) (3/10)          -- 1/2
-- Update that would go below gain_min without clamp
#eval gainCompressionUpdate (3/10) (-100) (1/100) (3/10)   -- 3/10 (clamped to gain_min)
-- Update that would go above 1 without clamp
#eval gainCompressionUpdate 1 (100) (1/100) (3/10)          -- 1 (clamped to 1)

/-! ## Summary of proved properties

  | Theorem                                    | Statement                                              | Status    |
  |--------------------------------------------|--------------------------------------------------------|-----------|
  | `constrainRat_ge_lo`                       | `constrainRat v lo hi ≥ lo` (given lo ≤ hi)            | ✅ Proved |
  | `constrainRat_le_hi`                       | `constrainRat v lo hi ≤ hi` (given lo ≤ hi)            | ✅ Proved |
  | `constrainRat_in_range`                    | `lo ≤ constrainRat v lo hi ≤ hi`                       | ✅ Proved |
  | `constrainRat_of_mem`                      | `lo ≤ v ≤ hi → constrainRat v lo hi = v` (identity)   | ✅ Proved |
  | `constrainRat_idempotent`                  | `constrainRat (constrainRat v lo hi) lo hi = …`        | ✅ Proved |
  | `gainCompressionUpdate_in_range`           | result ∈ [gain_min, 1] for any ka_dot, dt              | ✅ Proved |
  | `gainCompressionUpdate_ge_min`             | result ≥ gain_min                                      | ✅ Proved |
  | `gainCompressionUpdate_le_one`             | result ≤ 1                                             | ✅ Proved |
  | `gainCompressionIterate_in_range`          | ∀n steps, gain stays in [gain_min, 1]                  | ✅ Proved |
  | `gainCompression_leakage_positive`         | gain < 1 ∧ kLeakage > 0 → leakage > 0                 | ✅ Proved |
  | `gainCompression_leakage_at_max`           | leakage = 0 when gain = 1                              | ✅ Proved |
-/

end PX4.GainCompression
