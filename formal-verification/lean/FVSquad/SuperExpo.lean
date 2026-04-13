import FVSquad.Expo

/-!
# Formal Specification: superexpo (Super-Exponential RC Curve)

This file specifies and verifies the `superexpo` function used in PX4 for RC input
curve shaping. It extends `expo` with a "superrate" parameter `g` that boosts
sensitivity near ±1 while keeping the centre shape smooth.

## Source
`src/lib/mathlib/math/Functions.hpp` — `float superexpo(float value, float e, float g)`:
```cpp
template<typename T>
const T superexpo(const T &value, const T &e, const T &g)
{
    T x  = constrain(value, (T)-1, (T)1);
    T gc = constrain(g, (T)0, (T)0.99);
    return expo(x, e) * (1 - gc) / (1 - fabsf(x) * gc);
}
```

The denominator `1 - |x| * gc` is always positive: `|x| ≤ 1` and `gc ≤ 0.99 < 1`
imply `|x| * gc < 1`.  When `g = 0` the function reduces to `expo(value, e)`.

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `superexpo_denom_pos` | ✅ | denominator is always > 0 |
| `superexpo_zero` | ✅ | superexpo(0, e, g) = 0 |
| `superexpo_one` | ✅ | superexpo(1, e, g) = 1 |
| `superexpo_neg_one` | ✅ | superexpo(-1, e, g) = -1 |
| `superexpo_odd` | ✅ | anti-symmetry: superexpo(-v, e, g) = -superexpo(v, e, g) |
| `superexpo_in_range` | ✅ | output in [-1, 1] for any rational inputs |
| `superexpo_g_zero` | ✅ | g = 0 collapses to expo(v, e) |
| `superexpo_endpoints_fixed` | ✅ | ±1 are fixed points |

## Modelling Notes
- All arithmetic is over `Rat` (exact rationals), avoiding floating-point issues.
- `constrainRat` and `expoRat` are imported from `FVSquad.Expo`.
- `ratAbs x` models `fabsf(x)` applied to the already-clamped input.
- `gcMax = 99/100` is the upper bound for `g`, matching C++ `0.99f`.
- Lean's `Rat` division is total; the denominator is proved strictly positive.
-/

namespace PX4.SuperExpo

/-- Upper bound for the superrate parameter `g` (C++ clamps to `[0, 0.99f]`). -/
private def gcMax : Rat := 99 / 100

/-- Absolute value for rationals, modelling `fabsf(x)` in the C++ source. -/
private def ratAbs (x : Rat) : Rat := if 0 ≤ x then x else -x

/-- Rational model of the PX4 `superexpo` function.
    `superexpoRat v e g = expoRat(x, e) × (1-gc) / (1 - |x| × gc)`
    where `x = constrainRat v (-1) 1` and `gc = constrainRat g 0 (99/100)`. -/
def superexpoRat (v e g : Rat) : Rat :=
  let x  := constrainRat v (-1) 1
  let gc := constrainRat g 0 gcMax
  expoRat x e * (1 - gc) / (1 - ratAbs x * gc)

/-! ### Helper lemmas -/

private theorem ratAbs_nonneg (x : Rat) : 0 ≤ ratAbs x := by
  simp only [ratAbs]
  by_cases h : 0 ≤ x
  · simp [h]
  · simp [h]; exact Rat.le_of_lt (Rat.lt_neg_iff.mp (Rat.not_le.mp h))

private theorem ratAbs_neg (x : Rat) : ratAbs (-x) = ratAbs x := by
  simp only [ratAbs]
  by_cases h : 0 ≤ x
  · by_cases h2 : (0:Rat) ≤ -x
    · have hx_le : x ≤ 0 := by
        have := Rat.neg_le_neg h2; rw [Rat.neg_neg, Rat.neg_zero] at this; exact this
      simp [Rat.le_antisymm hx_le h]
    · rw [if_neg h2, if_pos h, Rat.neg_neg]
  · have hlt : x < 0 := Rat.not_le.mp h
    have hpos : 0 < -x := Rat.lt_neg_iff.mp hlt
    rw [if_pos (Rat.le_of_lt hpos), if_neg h]

private theorem ratAbs_le_one (x : Rat) (hlo : -1 ≤ x) (hhi : x ≤ 1) : ratAbs x ≤ 1 := by
  simp only [ratAbs]
  by_cases h : 0 ≤ x
  · simp [h]; exact hhi
  · simp [h]
    have := Rat.neg_le_neg hlo; rw [Rat.neg_neg] at this; exact this

/-- Re-proof of `constrain_neg_sym` (private in Expo.lean): clamping commutes with negation. -/
private theorem constrain_neg_sym' (v : Rat) :
    constrainRat (-v) (-1) 1 = -(constrainRat v (-1) 1) := by
  simp only [constrainRat]
  by_cases h1 : v < -1
  · have hv_neg : (1:Rat) < -v := Rat.neg_lt_neg h1
    have hv_neg_lo : (-1:Rat) ≤ -v := Rat.le_trans (by native_decide) (Rat.le_of_lt hv_neg)
    simp only [if_pos h1, if_neg (Rat.not_lt.mpr hv_neg_lo), if_pos hv_neg]
    native_decide
  · by_cases h2 : (1:Rat) < v
    · have h3 : (-v:Rat) < -1 := Rat.neg_lt_neg h2
      simp only [if_neg h1, if_pos h2, if_pos h3]
    · have hlo : (-1:Rat) ≤ v := Rat.not_lt.mp h1
      have hhi : v ≤ (1:Rat) := Rat.not_lt.mp h2
      have hclo : (-1:Rat) ≤ -v := by
        have h := Rat.neg_le_neg hhi
        have heq : (-1 : Rat) = -(1 : Rat) := by native_decide
        rw [heq]; exact h
      have hchi : -v ≤ (1:Rat) := by
        have := Rat.neg_le_neg hlo; rw [Rat.neg_neg] at this; exact this
      simp only [if_neg h1, if_neg h2,
                 if_neg (Rat.not_lt.mpr hclo), if_neg (Rat.not_lt.mpr hchi)]

/-- Helper: if `0 < d` and `n ≤ d` then `n / d ≤ 1`. -/
private theorem rat_div_le_one {n d : Rat} (hd : 0 < d) (hle : n ≤ d) : n / d ≤ 1 := by
  rw [Rat.div_def]
  have hdinv_nn : 0 ≤ d⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  have h := Rat.mul_le_mul_of_nonneg_right hle hdinv_nn
  rwa [Rat.mul_inv_cancel d (Rat.ne_of_gt hd)] at h

/-- Helper: if `0 < d` and `-d ≤ n` then `-1 ≤ n / d`. -/
private theorem rat_neg_one_le_div {n d : Rat} (hd : 0 < d) (hge : -d ≤ n) : -1 ≤ n / d := by
  rw [Rat.div_def]
  have hdinv_nn : 0 ≤ d⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  have h := Rat.mul_le_mul_of_nonneg_right hge hdinv_nn
  have hcancel : -d * d⁻¹ = -1 := by
    rw [Rat.neg_mul, Rat.mul_inv_cancel d (Rat.ne_of_gt hd)]
  rwa [hcancel] at h

/-- `gcMax = 99/100` is less than 1. -/
private theorem gcMax_lt_one : gcMax < 1 := by native_decide

/-- Any clamped `gc` satisfies `gc < 1`. -/
private theorem constrain_gc_lt_one (g : Rat) : constrainRat g 0 gcMax < 1 :=
  Std.lt_of_le_of_lt (constrainRat_le_hi g 0 gcMax (by native_decide)) gcMax_lt_one

/-! ### Main theorems -/

/-- The denominator `1 - |x| * gc` is always strictly positive. -/
theorem superexpo_denom_pos (v g : Rat) :
    0 < 1 - ratAbs (constrainRat v (-1) 1) * constrainRat g 0 gcMax := by
  have hx_lo := constrainRat_ge_lo v (-1) 1 (by native_decide)
  have hx_hi := constrainRat_le_hi v (-1) 1 (by native_decide)
  have hgc_lo := constrainRat_ge_lo g 0 gcMax (by native_decide)
  have habs_le : ratAbs (constrainRat v (-1) 1) ≤ 1 :=
    ratAbs_le_one _ hx_lo hx_hi
  have h1 : ratAbs (constrainRat v (-1) 1) * constrainRat g 0 gcMax ≤
            1 * constrainRat g 0 gcMax :=
    Rat.mul_le_mul_of_nonneg_right habs_le hgc_lo
  rw [Rat.one_mul] at h1
  have h3 : ratAbs (constrainRat v (-1) 1) * constrainRat g 0 gcMax ≤ gcMax :=
    Rat.le_trans h1 (constrainRat_le_hi g 0 gcMax (by native_decide))
  have h5 : ratAbs (constrainRat v (-1) 1) * constrainRat g 0 gcMax < 1 :=
    Std.lt_of_le_of_lt h3 gcMax_lt_one
  exact (Rat.lt_iff_sub_pos _ _).mp h5

/-- `superexpo(0, e, g) = 0` for any parameters. -/
theorem superexpo_zero (e g : Rat) : superexpoRat 0 e g = 0 := by
  simp only [superexpoRat]
  have hcv : constrainRat 0 (-1) 1 = 0 := by native_decide
  rw [hcv, expo_at_zero e, Rat.zero_mul, Rat.div_def, Rat.zero_mul]

/-- `superexpo(1, e, g) = 1`: the value 1 is always a fixed point. -/
theorem superexpo_one (e g : Rat) : superexpoRat 1 e g = 1 := by
  simp only [superexpoRat]
  have hcv : constrainRat 1 (-1) 1 = 1 := by native_decide
  rw [hcv, expo_at_pos_one e]
  have habs : ratAbs 1 = 1 := by
    simp only [ratAbs]; rw [if_pos (by native_decide : (0:Rat) ≤ 1)]
  rw [habs, Rat.one_mul, Rat.one_mul]
  -- Goal: (1 - constrainRat g 0 gcMax) / (1 - constrainRat g 0 gcMax) = 1
  have hgc_lt : constrainRat g 0 gcMax < 1 := constrain_gc_lt_one g
  have hdenom_pos : 0 < 1 - constrainRat g 0 gcMax :=
    (Rat.lt_iff_sub_pos (constrainRat g 0 gcMax) 1).mp hgc_lt
  rw [Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenom_pos)]

/-- `superexpo(-1, e, g) = -1`: the value -1 is always a fixed point. -/
theorem superexpo_neg_one (e g : Rat) : superexpoRat (-1) e g = -1 := by
  simp only [superexpoRat]
  have hcv : constrainRat (-1) (-1) 1 = -1 := by native_decide
  rw [hcv, expo_at_neg_one e]
  have habs : ratAbs (-1 : Rat) = 1 := by
    simp only [ratAbs]
    have h : ¬ (0:Rat) ≤ -1 := by native_decide
    rw [if_neg h]
    native_decide
  rw [habs, Rat.one_mul]
  -- Goal: -1 * (1 - gc) / (1 - gc) = -1
  have hgc_lt : constrainRat g 0 gcMax < 1 := constrain_gc_lt_one g
  have hdenom_pos : 0 < 1 - constrainRat g 0 gcMax :=
    (Rat.lt_iff_sub_pos (constrainRat g 0 gcMax) 1).mp hgc_lt
  have hdenom_ne : 1 - constrainRat g 0 gcMax ≠ 0 := Rat.ne_of_gt hdenom_pos
  rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hdenom_ne, Rat.mul_one]

/-- `superexpo` is an odd function: `superexpo(-v, e, g) = -superexpo(v, e, g)`.
    This preserves the sign of the stick input. -/
theorem superexpo_odd (v e g : Rat) : superexpoRat (-v) e g = -superexpoRat v e g := by
  simp only [superexpoRat]
  rw [constrain_neg_sym' v, expo_odd (constrainRat v (-1) 1) e,
      ratAbs_neg (constrainRat v (-1) 1)]
  -- Goal: -(expoRat cv e) * (1-gc) / (1-|cv|*gc) = -(expoRat cv e * (1-gc) / (1-|cv|*gc))
  rw [Rat.neg_mul, Rat.div_def, Rat.div_def, Rat.neg_mul]

/-- Core range proof: for any `x ∈ [-1,1]` and `gc ∈ [0, gcMax]`, the output is in `[-1,1]`. -/
private theorem superexpo_in_range_core (x gc : Rat) (e : Rat)
    (hx_lo : (-1:Rat) ≤ x) (hx_hi : x ≤ 1)
    (hgc_lo : (0:Rat) ≤ gc) (hgc_hi : gc ≤ gcMax) :
    -1 ≤ expoRat x e * (1 - gc) / (1 - ratAbs x * gc) ∧
    expoRat x e * (1 - gc) / (1 - ratAbs x * gc) ≤ 1 := by
  have hf_range := expo_in_range x e
  have hf_lo : (-1:Rat) ≤ expoRat x e := hf_range.1
  have hf_hi : expoRat x e ≤ 1 := hf_range.2
  have habs_le : ratAbs x ≤ 1 := ratAbs_le_one x hx_lo hx_hi
  have habs_nn := ratAbs_nonneg x
  -- 0 ≤ 1 - gc (since gc < 1)
  have hgc_lt : gc < 1 := Std.lt_of_le_of_lt hgc_hi gcMax_lt_one
  have hone_gc_nn : (0:Rat) ≤ 1 - gc :=
    Rat.le_of_lt ((Rat.lt_iff_sub_pos gc 1).mp hgc_lt)
  -- 0 < denom = 1 - |x|*gc
  have h_abs_gc : ratAbs x * gc ≤ gc := by
    have h := Rat.mul_le_mul_of_nonneg_right habs_le hgc_lo
    rwa [Rat.one_mul] at h
  have hdenom_pos : 0 < 1 - ratAbs x * gc := by
    have h_prod_lt : ratAbs x * gc < 1 :=
      Std.lt_of_le_of_lt (Rat.le_trans h_abs_gc hgc_hi) gcMax_lt_one
    exact (Rat.lt_iff_sub_pos _ _).mp h_prod_lt
  -- (1-gc) ≤ (1 - |x|*gc) since |x|*gc ≤ gc
  have hone_gc_le_denom : 1 - gc ≤ 1 - ratAbs x * gc := by
    have := Rat.neg_le_neg h_abs_gc
    simp only [Rat.sub_eq_add_neg]
    exact Rat.add_le_add_left.mpr this
  -- upper bound: expoRat x e * (1-gc) ≤ denom
  have hnumer_le_denom : expoRat x e * (1 - gc) ≤ 1 - ratAbs x * gc := by
    have h1 : expoRat x e * (1 - gc) ≤ 1 * (1 - gc) :=
      Rat.mul_le_mul_of_nonneg_right hf_hi hone_gc_nn
    rw [Rat.one_mul] at h1; exact Rat.le_trans h1 hone_gc_le_denom
  -- lower bound: -denom ≤ expoRat x e * (1-gc)
  have hneg_denom_le_numer : -(1 - ratAbs x * gc) ≤ expoRat x e * (1 - gc) := by
    have h1 : (-1) * (1 - gc) ≤ expoRat x e * (1 - gc) :=
      Rat.mul_le_mul_of_nonneg_right hf_lo hone_gc_nn
    have h_neg_gc : -(1 - gc) ≤ expoRat x e * (1 - gc) := by
      rwa [show (-1 : Rat) * (1 - gc) = -(1 - gc) from by rw [Rat.neg_mul, Rat.one_mul]] at h1
    exact Rat.le_trans (Rat.neg_le_neg hone_gc_le_denom) h_neg_gc
  exact ⟨rat_neg_one_le_div hdenom_pos hneg_denom_le_numer,
         rat_div_le_one hdenom_pos hnumer_le_denom⟩

/-- The output of `superexpo` lies in `[-1, 1]` for any rational inputs. -/
theorem superexpo_in_range (v e g : Rat) :
    -1 ≤ superexpoRat v e g ∧ superexpoRat v e g ≤ 1 := by
  simp only [superexpoRat]
  exact superexpo_in_range_core
    (constrainRat v (-1) 1) (constrainRat g 0 gcMax) e
    (constrainRat_ge_lo v (-1) 1 (by native_decide))
    (constrainRat_le_hi v (-1) 1 (by native_decide))
    (constrainRat_ge_lo g 0 gcMax (by native_decide))
    (constrainRat_le_hi g 0 gcMax (by native_decide))

/-- When `g = 0`, `superexpo(v, e, 0) = expo(v, e)`. -/
theorem superexpo_g_zero (v e : Rat) : superexpoRat v e 0 = expoRat v e := by
  simp only [superexpoRat]
  have hgc : constrainRat 0 0 gcMax = 0 := by apply constrainRat_id <;> native_decide
  rw [hgc, Rat.mul_zero]
  have h1 : (1 : Rat) - 0 = 1 := by native_decide
  rw [h1, Rat.mul_one, Rat.div_def, show (1 : Rat)⁻¹ = 1 from by native_decide, Rat.mul_one]
  -- Goal: expoRat (constrainRat v (-1) 1) e = expoRat v e
  have hcv_idem : constrainRat (constrainRat v (-1) 1) (-1) 1 = constrainRat v (-1) 1 :=
    constrainRat_id _ _ _
      (constrainRat_ge_lo v (-1) 1 (by native_decide))
      (constrainRat_le_hi v (-1) 1 (by native_decide))
  simp only [expoRat, hcv_idem]

/-- Both `1` and `-1` are fixed points of `superexpo`. -/
theorem superexpo_endpoints_fixed (e g : Rat) :
    superexpoRat 1 e g = 1 ∧ superexpoRat (-1) e g = -1 :=
  ⟨superexpo_one e g, superexpo_neg_one e g⟩

end PX4.SuperExpo
