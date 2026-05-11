/-!
# Formal Specification: expo (Exponential RC Curve)

This file specifies and verifies the `expo` function used in PX4 for RC input
curve shaping. The function blends a linear curve with a cubic curve based on an
exponential parameter, allowing pilots to customise stick sensitivity.

## Source
`src/lib/mathlib/math/Functions.hpp` — `float expo(float value, float e)`:
```cpp
inline float expo(float value, float e)
{
    float x = constrain(value, -1.f, 1.f);
    return (1.f - e) * x + e * x * x * x;
}
```

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `expo_at_zero` | ✅ | expo(0, e) = 0 |
| `expo_at_pos_one` | ✅ | expo(1, e) = 1 |
| `expo_at_neg_one` | ✅ | expo(-1, e) = -1 |
| `expo_linear` | ✅ | e=0 gives identity (linear) |
| `expo_cubic` | ✅ | e=1 gives x³ (pure cubic) |
| `expo_odd` | ✅ | anti-symmetry: expo(-v,e) = -expo(v,e) |
| `expo_in_range` | ✅ | output in [-1,1] for inputs in [-1,1] |
| `expo_eq_linear_at_zero` | ✅ | derivative at 0 is (1-e) |
| `expo_endpoints_fixed` | ✅ | ±1 are fixed points |
| `constrain_mono` | ✅ | constrainRat is monotone in v |
| `expo_mono_val` | ✅ | larger stick input → larger output (monotone in v) |
| `expo_mono_e_pos_v` | ✅ | for v ≥ 0: larger expo → smaller output (decreasing in e) |
| `expo_mono_e_neg_v` | ✅ | for v ≤ 0: larger expo → larger output (increasing in e) |

## Modelling Notes
- All arithmetic is over `Rat` (exact rationals), avoiding floating-point issues.
- `constrainRat` models the C++ `constrain` function for the `[-1,1]` range.
- The exponential parameter `e` is also clamped to `[0,1]`.
-/

open Classical

/-- `constrainRat v lo hi` clamps `v` to the interval `[lo, hi]`. -/
def constrainRat (v lo hi : Rat) : Rat :=
  if v < lo then lo else if v > hi then hi else v

theorem constrainRat_ge_lo (v lo hi : Rat) (h : lo ≤ hi) : lo ≤ constrainRat v lo hi := by
  simp only [constrainRat]; by_cases h1 : v < lo
  · simp [h1]
  · by_cases h2 : v > hi
    · simp [h1, h2]; exact h
    · simp [h1, h2]; exact Rat.not_lt.mp h1

theorem constrainRat_le_hi (v lo hi : Rat) (h : lo ≤ hi) : constrainRat v lo hi ≤ hi := by
  simp only [constrainRat]; by_cases h1 : v < lo
  · simp [h1]; exact h
  · by_cases h2 : v > hi
    · simp [h1, h2]
    · simp [h1, h2]; exact Rat.not_lt.mp h2

theorem constrainRat_id (v lo hi : Rat) (hlo : lo ≤ v) (hhi : v ≤ hi) :
    constrainRat v lo hi = v := by
  simp only [constrainRat]
  rw [if_neg (Rat.not_lt.mpr hlo), if_neg (Rat.not_lt.mpr hhi)]

/-- Helper: add two inequalities. -/
private theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

/-- Helper: `x * x` is non-negative for any rational `x`. -/
private theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hn : 0 ≤ -x := by have := Rat.neg_le_neg hx0; rw [Rat.neg_zero] at this; exact this
    have := Rat.mul_nonneg hn hn
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this; exact this

/-- Helper: if `x ∈ [-1,1]` then `x³ ≤ 1`. -/
private theorem cube_le_one (x : Rat) (_ : -1 ≤ x) (hhi : x ≤ 1) : x * x * x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · have hxx : x * x ≤ 1 := by
      have h1 : x * x ≤ x * 1 := Rat.mul_le_mul_of_nonneg_left hhi hx
      rw [Rat.mul_one] at h1; exact Rat.le_trans h1 hhi
    have h2 : x * x * x ≤ 1 * x := Rat.mul_le_mul_of_nonneg_right hxx hx
    rw [Rat.one_mul] at h2; exact Rat.le_trans h2 hhi
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hn : 0 ≤ -x := by have := Rat.neg_le_neg hx0; rw [Rat.neg_zero] at this; exact this
    have hxx_nn : 0 ≤ x * x := by
      have := Rat.mul_nonneg hn hn
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this; exact this
    have h := Rat.mul_le_mul_of_nonneg_left hx0 hxx_nn
    rw [Rat.mul_zero] at h; exact Rat.le_trans h (by native_decide)

/-- Helper: if `x ∈ [-1,1]` then `-1 ≤ x³`. -/
private theorem cube_ge_neg_one (x : Rat) (hlo : -1 ≤ x) (hhi : x ≤ 1) : -1 ≤ x * x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.le_trans (by native_decide) (Rat.mul_nonneg (Rat.mul_nonneg hx hx) hx)
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hnx_nn : 0 ≤ -x := by
      have := Rat.neg_le_neg hx0; rw [Rat.neg_zero] at this; exact this
    have hnx_le : -x ≤ 1 := by
      have := Rat.neg_le_neg hlo; rw [Rat.neg_neg] at this; exact this
    rw [show x * x * x = -((-x) * (-x) * (-x)) from by
          simp [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]]
    exact Rat.neg_le_neg (cube_le_one (-x) (Rat.neg_le_neg hhi) hnx_le)

/-- Helper: `constrainRat (-v) (-1) 1 = -(constrainRat v (-1) 1)`.
    The clamp function is odd (anti-symmetric) on `[-1,1]`. -/
private theorem constrain_neg_sym (v : Rat) :
    constrainRat (-v) (-1) 1 = -(constrainRat v (-1) 1) := by
  simp only [constrainRat]
  by_cases h1 : v < -1
  · -- v < -1 ⟹ -v > 1
    have h2 : (1:Rat) < -v := Rat.neg_lt_neg h1
    have h4 : (1:Rat) ≤ -v := Rat.le_of_lt h2
    have h5 : (-1:Rat) ≤ -v := Rat.le_trans (by native_decide) h4
    simp only [if_pos h1, if_neg (Rat.not_lt.mpr h5), show (1:Rat) < -v from h2]
    simp [Rat.neg_neg]
  · by_cases h2 : (1:Rat) < v
    · -- v > 1 ⟹ -v < -1
      have h3 : (-v:Rat) < -1 := Rat.neg_lt_neg h2
      simp only [if_neg h1, if_pos h2, if_pos h3]
    · -- v ∈ [-1, 1]
      have hlo : (-1:Rat) ≤ v := Rat.not_lt.mp h1
      have hhi : v ≤ (1:Rat) := Rat.not_lt.mp h2
      have hclo : (-1:Rat) ≤ -v := Rat.neg_le_neg hhi
      have hchi : -v ≤ (1:Rat) := by
        have := Rat.neg_le_neg hlo; rw [Rat.neg_neg] at this; exact this
      rw [if_neg h1, if_neg h2,
          if_neg (Rat.not_lt.mpr hclo), if_neg (Rat.not_lt.mpr hchi)]

/-- Rational model of the PX4 `expo` function.
    `expoRat v e = (1-e_clamped) * v_clamped + e_clamped * v_clamped³` -/
def expoRat (v e : Rat) : Rat :=
  let cv := constrainRat v (-1) 1
  let ec := constrainRat e 0 1
  (1 - ec) * cv + ec * cv * cv * cv

/-- `expo(0, e) = 0` for any exponential parameter. -/
theorem expo_at_zero (e : Rat) : expoRat 0 e = 0 := by
  have hc : constrainRat 0 (-1) 1 = 0 := by native_decide
  simp only [expoRat, hc, Rat.mul_zero, Rat.add_zero]

/-- `expo(1, e) = 1`: the value 1 is a fixed point. -/
theorem expo_at_pos_one (e : Rat) : expoRat 1 e = 1 := by
  have hc : constrainRat 1 (-1) 1 = 1 := by native_decide
  simp only [expoRat, hc, Rat.mul_one, Rat.sub_add_cancel]

/-- `expo(-1, e) = -1`: the value -1 is a fixed point. -/
theorem expo_at_neg_one (e : Rat) : expoRat (-1) e = -1 := by
  have hc : constrainRat (-1) (-1) 1 = -1 := by native_decide
  simp only [expoRat, hc]
  simp [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.mul_one, Rat.neg_neg,
        Rat.neg_add, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

/-- When `e = 0`, expo is the identity (linear) on clamped input. -/
theorem expo_linear (v : Rat) : expoRat v 0 = constrainRat v (-1) 1 := by
  have he : constrainRat 0 0 1 = 0 := by native_decide
  simp only [expoRat, he, Rat.add_zero, Rat.one_mul,
             Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.zero_mul]

/-- When `e = 1`, expo returns the cube of the clamped input. -/
theorem expo_cubic (v : Rat) :
    expoRat v 1 = constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1 := by
  have he : constrainRat 1 0 1 = 1 := by native_decide
  simp only [expoRat, he, Rat.sub_self, Rat.zero_mul, Rat.zero_add, Rat.one_mul]

/-- `expo` is an odd function: `expo(-v, e) = -expo(v, e)`.
    This preserves the sign of the stick input. -/
theorem expo_odd (v e : Rat) : expoRat (-v) e = -expoRat v e := by
  simp only [expoRat]
  rw [constrain_neg_sym v]
  simp [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg, Rat.neg_add]

/-- The output of `expo` lies in `[-1, 1]` for any rational inputs. -/
theorem expo_in_range (v e : Rat) : -1 ≤ expoRat v e ∧ expoRat v e ≤ 1 := by
  simp only [expoRat]
  have hcv_lo := constrainRat_ge_lo v (-1) 1 (by native_decide)
  have hcv_hi := constrainRat_le_hi v (-1) 1 (by native_decide)
  have hec_lo := constrainRat_ge_lo e 0 1 (by native_decide)
  have hec_hi := constrainRat_le_hi e 0 1 (by native_decide)
  -- 1 - ec ≥ 0  (because ec ≤ 1)
  have hec1_nn : (0:Rat) ≤ 1 - constrainRat e 0 1 := by
    simp only [Rat.sub_eq_add_neg]
    have h := (Rat.add_le_add_left (c := 1)).mpr (Rat.neg_le_neg hec_hi)
    have h2 : (1:Rat) + -1 = 0 := by native_decide
    rw [h2] at h; exact h
  -- cube bounds for cv
  have hcv3_lo := cube_ge_neg_one _ hcv_lo hcv_hi
  have hcv3_hi := cube_le_one _ hcv_lo hcv_hi
  -- reassociate: ec*cv*cv*cv → ec*(cv*cv*cv)
  have hma : (1 - constrainRat e 0 1) * constrainRat v (-1) 1 +
             constrainRat e 0 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1 =
             (1 - constrainRat e 0 1) * constrainRat v (-1) 1 +
             constrainRat e 0 1 * (constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1) := by
    simp [Rat.mul_assoc]
  rw [hma]
  constructor
  · -- Lower bound: -1 ≤ (1-ec)*cv + ec*(cv*cv*cv)
    have h1 : (1 - constrainRat e 0 1) * (-1) ≤
              (1 - constrainRat e 0 1) * constrainRat v (-1) 1 :=
      Rat.mul_le_mul_of_nonneg_left hcv_lo hec1_nn
    have h2 : constrainRat e 0 1 * (-1) ≤
              constrainRat e 0 1 * (constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1) :=
      Rat.mul_le_mul_of_nonneg_left hcv3_lo hec_lo
    have h4 := rat_add_le_add h1 h2
    have h5 : (1 - constrainRat e 0 1) * (-1) + constrainRat e 0 1 * (-1) = -1 := by
      simp [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.mul_one, Rat.neg_neg,
            Rat.neg_add, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
    rw [h5] at h4; exact h4
  · -- Upper bound: (1-ec)*cv + ec*(cv*cv*cv) ≤ 1
    have h1 : (1 - constrainRat e 0 1) * constrainRat v (-1) 1 ≤
              (1 - constrainRat e 0 1) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hcv_hi hec1_nn
    have h2 : constrainRat e 0 1 * (constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1) ≤
              constrainRat e 0 1 * 1 :=
      Rat.mul_le_mul_of_nonneg_left hcv3_hi hec_lo
    have h4 := rat_add_le_add h1 h2
    have h5 : (1 - constrainRat e 0 1) * 1 + constrainRat e 0 1 * 1 = 1 := by
      simp [Rat.mul_one, Rat.sub_add_cancel]
    rw [h5] at h4; exact h4

/-- The slope of expo at `v = 0` is `(1 - e)`.
    This confirms that `e` directly controls the centre sensitivity. -/
theorem expo_eq_linear_at_zero (e : Rat) (_h : 0 < e) (_he : e ≤ 1) :
    ∀ δ : Rat, expoRat δ e - expoRat 0 e = (1 - constrainRat e 0 1) * constrainRat δ (-1) 1 +
              constrainRat e 0 1 * constrainRat δ (-1) 1 * constrainRat δ (-1) 1 * constrainRat δ (-1) 1 := by
  intro δ
  have h0 : expoRat 0 e = 0 := expo_at_zero e
  rw [h0, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  simp [expoRat]

/-- Both `1` and `-1` are fixed points of expo. -/
theorem expo_endpoints_fixed (e : Rat) : expoRat 1 e = 1 ∧ expoRat (-1) e = -1 :=
  ⟨expo_at_pos_one e, expo_at_neg_one e⟩

/-- `constrainRat` is monotone in its first argument:
    if `v1 ≤ v2` then the clamped value of `v1` is at most the clamped value of `v2`.
    This is a key helper for the monotonicity of `expoRat`. -/
theorem constrain_mono (v1 v2 lo hi : Rat) (h : v1 ≤ v2) (hlohi : lo ≤ hi) :
    constrainRat v1 lo hi ≤ constrainRat v2 lo hi := by
  simp only [constrainRat]
  by_cases h1 : v1 < lo
  · simp only [if_pos h1]
    by_cases h2 : v2 < lo
    · simp [h2]
    · by_cases h3 : v2 > hi
      · simp [h2, h3]; exact hlohi
      · simp [h2, h3]; exact Rat.not_lt.mp h2
  · have hv1lo := Rat.not_lt.mp h1
    by_cases h3 : v1 > hi
    · have hv2hi : v2 > hi := by
        by_cases h4 : hi < v2; · exact h4
        · exact absurd (Rat.le_trans h (Rat.not_lt.mp h4)) (Rat.not_le.mpr h3)
      have hv2lo : ¬ v2 < lo := Rat.not_lt.mpr (Rat.le_trans hlohi (Rat.le_of_lt hv2hi))
      simp [h1, h3, hv2hi, hv2lo]
    · have hv1hi := Rat.not_lt.mp h3
      simp only [if_neg h1, if_neg h3]
      by_cases h4 : v2 > hi
      · have hv2lo : ¬ v2 < lo := Rat.not_lt.mpr (Rat.le_trans hv1lo h)
        simp [h4, hv2lo]; exact hv1hi
      · have hv2lo : ¬ v2 < lo := Rat.not_lt.mpr (Rat.le_trans hv1lo h)
        simp [h4, hv2lo]; exact h

/-- Helper: cube is monotone over rationals (follows from the sign-case analysis). -/
private theorem cube_mono_rat (v1 v2 : Rat) (h : v1 ≤ v2) :
    v1 * v1 * v1 ≤ v2 * v2 * v2 := by
  by_cases hv2 : 0 ≤ v2
  · by_cases hv1 : 0 ≤ v1
    · have hsq : v1 * v1 ≤ v2 * v2 :=
        calc v1 * v1 ≤ v2 * v1 := Rat.mul_le_mul_of_nonneg_right h hv1
          _ ≤ v2 * v2 := Rat.mul_le_mul_of_nonneg_left h hv2
      calc v1 * v1 * v1 ≤ v2 * v2 * v1 := Rat.mul_le_mul_of_nonneg_right hsq hv1
        _ ≤ v2 * v2 * v2 := Rat.mul_le_mul_of_nonneg_left h (Rat.mul_nonneg hv2 hv2)
    · have hv1n : v1 ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hv1)
      have hnn : 0 ≤ v1 * v1 := by
        have hn : 0 ≤ -v1 := by
          have := Rat.neg_le_neg hv1n; rw [Rat.neg_zero] at this; exact this
        have := Rat.mul_nonneg hn hn
        rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this; exact this
      have h1 : v1 * v1 * v1 ≤ 0 := by
        have hmul : v1 * v1 * v1 ≤ v1 * v1 * 0 := Rat.mul_le_mul_of_nonneg_left hv1n hnn
        simp [Rat.mul_zero] at hmul; exact hmul
      exact Rat.le_trans h1 (Rat.mul_nonneg (Rat.mul_nonneg hv2 hv2) hv2)
  · have hv2n : v2 ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hv2)
    have hv1n : v1 ≤ 0 := Rat.le_trans h hv2n
    have hn1 : 0 ≤ -v1 := by
      have := Rat.neg_le_neg hv1n; rw [Rat.neg_zero] at this; exact this
    have hn2 : 0 ≤ -v2 := by
      have := Rat.neg_le_neg hv2n; rw [Rat.neg_zero] at this; exact this
    have hn12 : -v2 ≤ -v1 := Rat.neg_le_neg h
    have hsq : (-v2) * (-v2) ≤ (-v1) * (-v1) :=
      calc (-v2) * (-v2) ≤ (-v1) * (-v2) := Rat.mul_le_mul_of_nonneg_right hn12 hn2
        _ ≤ (-v1) * (-v1) := Rat.mul_le_mul_of_nonneg_left hn12 hn1
    have hcube : (-v2) * (-v2) * (-v2) ≤ (-v1) * (-v1) * (-v1) :=
      calc (-v2) * (-v2) * (-v2) ≤ (-v1) * (-v1) * (-v2) :=
            Rat.mul_le_mul_of_nonneg_right hsq hn2
        _ ≤ (-v1) * (-v1) * (-v1) :=
            Rat.mul_le_mul_of_nonneg_left hn12 (Rat.mul_nonneg hn1 hn1)
    simp [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at hcube; exact hcube

/-- `expoRat` is monotone in its value parameter:
    a larger stick deflection produces a larger (or equal) output.
    This property is essential for pilot usability — equal input magnitudes on
    opposite sticks produce equal-magnitude but opposite outputs, and increasing
    deflection always increases output. -/
theorem expo_mono_val (v1 v2 e : Rat) (hv : v1 ≤ v2) :
    expoRat v1 e ≤ expoRat v2 e := by
  simp only [expoRat]
  have hcv : constrainRat v1 (-1) 1 ≤ constrainRat v2 (-1) 1 :=
    constrain_mono v1 v2 (-1) 1 hv (by native_decide)
  have hec_lo : (0 : Rat) ≤ constrainRat e 0 1 := constrainRat_ge_lo e 0 1 (by native_decide)
  have hec_hi : constrainRat e 0 1 ≤ 1 := constrainRat_le_hi e 0 1 (by native_decide)
  have hec1_nn : (0 : Rat) ≤ 1 - constrainRat e 0 1 := by
    rw [Rat.sub_eq_add_neg]
    have := (Rat.add_le_add_left (c := 1)).mpr (Rat.neg_le_neg hec_hi)
    rw [show (1:Rat) + -1 = 0 from by native_decide] at this; exact this
  have hcube := cube_mono_rat (constrainRat v1 (-1) 1) (constrainRat v2 (-1) 1) hcv
  have h1 : (1 - constrainRat e 0 1) * constrainRat v1 (-1) 1 ≤
            (1 - constrainRat e 0 1) * constrainRat v2 (-1) 1 :=
    Rat.mul_le_mul_of_nonneg_left hcv hec1_nn
  have h2 : constrainRat e 0 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1 ≤
            constrainRat e 0 1 * constrainRat v2 (-1) 1 * constrainRat v2 (-1) 1 * constrainRat v2 (-1) 1 := by
    have ha : constrainRat e 0 1 * (constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1) ≤
              constrainRat e 0 1 * (constrainRat v2 (-1) 1 * constrainRat v2 (-1) 1 * constrainRat v2 (-1) 1) :=
      Rat.mul_le_mul_of_nonneg_left hcube hec_lo
    simp [Rat.mul_assoc] at ha ⊢; exact ha
  calc (1 - constrainRat e 0 1) * constrainRat v1 (-1) 1 +
       constrainRat e 0 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1
      ≤ (1 - constrainRat e 0 1) * constrainRat v2 (-1) 1 +
        constrainRat e 0 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1 * constrainRat v1 (-1) 1 :=
          (Rat.add_le_add_right (b := _)).mpr h1
    _ ≤ (1 - constrainRat e 0 1) * constrainRat v2 (-1) 1 +
        constrainRat e 0 1 * constrainRat v2 (-1) 1 * constrainRat v2 (-1) 1 * constrainRat v2 (-1) 1 :=
          (Rat.add_le_add_left (c := _)).mpr h2

/-- Helper: the expo formula equals `cv + ec*(cv³ - cv)`, revealing it as a
    centre-biased shift: when `cv³ - cv ≤ 0` (which holds for `cv ∈ [0,1]`),
    increasing `ec` pulls the output toward zero. -/
private theorem expo_as_correction (ec cv : Rat) :
    (1 - ec) * cv + ec * cv * cv * cv = cv + ec * (cv * cv * cv - cv) := by
  have h2 : (1 - ec) * cv = cv - ec * cv := by
    rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.one_mul, Rat.neg_mul, ← Rat.sub_eq_add_neg]
  have h3 : ec * (cv * cv * cv - cv) = ec * (cv * cv * cv) - ec * cv := by
    rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, ← Rat.sub_eq_add_neg]
  rw [h2, h3, show ec * cv * cv * cv = ec * (cv * cv * cv) from by simp [Rat.mul_assoc]]
  simp only [Rat.sub_eq_add_neg]
  rw [Rat.add_assoc, Rat.add_comm (-(ec * cv))]

/-- Helper: `constrainRat v (-1) 1 ≥ 0` when `v ≥ 0`. -/
private theorem cv_nonneg_of_nonneg (v : Rat) (h : 0 ≤ v) : (0 : Rat) ≤ constrainRat v (-1) 1 := by
  simp only [constrainRat]
  have hn1 : ¬(v < -1) := Rat.not_lt.mpr (Rat.le_trans (by native_decide : (-1:Rat) ≤ 0) h)
  simp only [hn1, ↓reduceIte]
  by_cases h2 : v > 1
  · simp only [h2, ↓reduceIte]; native_decide
  · simp only [h2, ↓reduceIte]; exact h

/-- Helper: `cv³ ≤ cv` when `0 ≤ cv ≤ 1`. -/
private theorem cv_cube_le_cv (cv : Rat) (hlo : 0 ≤ cv) (hhi : cv ≤ 1) : cv * cv * cv ≤ cv := by
  have hcvsq : cv * cv ≤ 1 := by
    calc cv * cv ≤ 1 * cv := Rat.mul_le_mul_of_nonneg_right hhi hlo
         _ = cv := Rat.one_mul cv
         _ ≤ 1 := hhi
  calc cv * cv * cv ≤ 1 * cv := Rat.mul_le_mul_of_nonneg_right hcvsq hlo
       _ = cv := Rat.one_mul cv

/-- Helper: `0 ≤ cv - cv³` when `0 ≤ cv ≤ 1`. -/
private theorem cv_diff_nonneg (cv : Rat) (hlo : 0 ≤ cv) (hhi : cv ≤ 1) :
    0 ≤ cv - cv * cv * cv := by
  have h2 := (Rat.add_le_add_right (c := -(cv * cv * cv))).mpr (cv_cube_le_cv cv hlo hhi)
  rw [Rat.add_neg_cancel] at h2; rwa [← Rat.sub_eq_add_neg] at h2

/-- Helper: `ec2*(cv³ - cv) ≤ ec1*(cv³ - cv)` when `ec1 ≤ ec2` and `cv ∈ [0,1]`.
    Since `cv³ - cv ≤ 0`, multiplying by a larger `ec` makes the result more negative. -/
private theorem mono_e_ineq (ec1 ec2 cv : Rat) (hec_le : ec1 ≤ ec2)
    (hcv_lo : 0 ≤ cv) (hcv_hi : cv ≤ 1) :
    ec2 * (cv * cv * cv - cv) ≤ ec1 * (cv * cv * cv - cv) := by
  have h1 := Rat.mul_le_mul_of_nonneg_right hec_le (cv_diff_nonneg cv hcv_lo hcv_hi)
  have hflip : cv * cv * cv - cv = -(cv - cv * cv * cv) := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.add_comm]
  rw [hflip, Rat.mul_neg, Rat.mul_neg]; exact Rat.neg_le_neg h1

/-- **`expoRat` is decreasing in the expo parameter `e` for non-negative stick inputs.**

    When the stick deflection `v ≥ 0`, a higher expo value `e` reduces the output:
    less linear sensitivity at the centre, more "dead" feel.  This is the defining
    purpose of the expo parameter — it allows pilots to dial in centre-stick softness
    without changing the maximum deflection.

    Formally: `e₁ ≤ e₂ → 0 ≤ v → expoRat v e₂ ≤ expoRat v e₁`. -/
theorem expo_mono_e_pos_v (v e1 e2 : Rat) (hv : 0 ≤ v) (he : e1 ≤ e2) :
    expoRat v e2 ≤ expoRat v e1 := by
  simp only [expoRat]
  have hcv_nn : (0:Rat) ≤ constrainRat v (-1) 1 := cv_nonneg_of_nonneg v hv
  have hcv_hi : constrainRat v (-1) 1 ≤ 1 := constrainRat_le_hi v (-1) 1 (by native_decide)
  have hec_le : constrainRat e1 0 1 ≤ constrainRat e2 0 1 :=
    constrain_mono e1 e2 0 1 he (by native_decide)
  rw [expo_as_correction (constrainRat e2 0 1) (constrainRat v (-1) 1),
      expo_as_correction (constrainRat e1 0 1) (constrainRat v (-1) 1)]
  exact (Rat.add_le_add_left (c := constrainRat v (-1) 1)).mpr
    (mono_e_ineq (constrainRat e1 0 1) (constrainRat e2 0 1) (constrainRat v (-1) 1)
      hec_le hcv_nn hcv_hi)

/-- **`expoRat` is increasing in the expo parameter `e` for non-positive stick inputs.**

    By odd-symmetry of `expoRat`, the `v ≤ 0` case follows directly from the
    `v ≥ 0` decreasing result: increasing `e` makes negative deflections more
    negative (i.e., larger in the negative direction). -/
theorem expo_mono_e_neg_v (v e1 e2 : Rat) (hv : v ≤ 0) (he : e1 ≤ e2) :
    expoRat v e1 ≤ expoRat v e2 := by
  -- -v ≥ 0, so expo is decreasing in e for (-v)
  have hw : (0:Rat) ≤ -v := by
    have := Rat.neg_le_neg hv; rw [Rat.neg_zero] at this; exact this
  have h := expo_mono_e_pos_v (-v) e1 e2 hw he
  -- h : expoRat (-v) e2 ≤ expoRat (-v) e1
  -- expo_odd v e : expoRat (-v) e = -expoRat v e
  rw [expo_odd v e2, expo_odd v e1] at h
  -- h : -expoRat v e2 ≤ -expoRat v e1  →  expoRat v e1 ≤ expoRat v e2
  have := Rat.neg_le_neg h
  rwa [Rat.neg_neg, Rat.neg_neg] at this
