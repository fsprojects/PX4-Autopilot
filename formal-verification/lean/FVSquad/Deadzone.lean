/-!
# PX4 Deadzone Function — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::deadzone` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`
- **Informal spec**: `formal-verification/specs/deadzone_informal.md`

## Model

We model the function over `Rat` (rational numbers) to capture exact piecewise-linear
semantics.  The C++ implementation uses `float`; our model is an exact abstraction.

```cpp
// C++ (condensed):
const T deadzone(const T &value, const T &dz) {
  T x   = constrain(value, -1, 1);
  T dzc = constrain(dz, 0, 0.99);
  T out = (x - sign(x) * dzc) / (1 - dzc);
  return out * (fabsf(x) > dzc);   // zeroed in deadzone
}
```

## Approximations / out of scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Input clamping**: we assume inputs are already in range (`|x| ≤ 1`, `0 ≤ dz < 1`).
  The internal `constrain` calls are not modelled.
- **`dz` upper bound**: C++ uses `0.99`; we allow any `dz < 1`.

## What Cannot Be Proved Without Mathlib

Several arithmetic lemmas below require `linarith` or `ring` over `Rat`, which are
only available via Mathlib. Those theorems are marked with `sorry` and a comment.
Install Mathlib (add `require mathlib` to `lakefile.toml`) to unlock full proofs.
-/

namespace PX4.Deadzone

/-- Rational sign: +1 when `x ≥ 0`, −1 when `x < 0`. -/
def signR (x : Rat) : Rat := if 0 ≤ x then 1 else -1

/-- Pure functional model of `math::deadzone` over `Rat`.

    - When `|x| ≤ dz` (inside deadzone): returns `0`.
    - When `|x| > dz` (outside deadzone): returns `(x − sign(x)·dz) / (1 − dz)`. -/
def deadzone (x dz : Rat) : Rat :=
  if x.abs > dz then (x - signR x * dz) / (1 - dz) else 0

-- Sanity check: model produces expected numeric outputs.
#eval deadzone 0      0.3   -- 0      (inside deadzone)
#eval deadzone 0.3    0.3   -- 0      (on boundary — inclusive deadzone)
#eval deadzone 0.5    0.3   -- 2/7    ≈ 0.286
#eval deadzone 1      0.3   -- 1      (extreme input → extreme output)
#eval deadzone (-0.5) 0.3   -- -2/7   (negative, symmetric)
#eval deadzone (-1)   0.3   -- -1
#eval deadzone 0.5    0     -- 1/2    (no deadzone → identity)

/-! ## signR lemmas -/

/-- `signR x = 1` when `x ≥ 0`. -/
theorem signR_of_nonneg (x : Rat) (h : 0 ≤ x) : signR x = 1 := by
  simp [signR, h]

/-- `signR x = −1` when `x < 0`. -/
theorem signR_of_neg (x : Rat) (h : x < 0) : signR x = -1 := by
  simp [signR, show ¬(0 ≤ x) from Rat.not_le.mpr h]

/-! ## Structural theorem: in-deadzone outputs 0 -/

/-- The central deadzone property: any input inside the deadzone maps to exactly 0.

    This holds with equality — there is no rounding or approximation.
    `|x| ≤ dz → deadzone x dz = 0` -/
theorem deadzone_in_dz (x dz : Rat) (h : x.abs ≤ dz) :
    deadzone x dz = 0 := by
  simp only [deadzone]
  rw [if_neg (Rat.not_lt.mpr h)]

/-! ## Simplified form outside the deadzone -/

/-- When `x > dz ≥ 0`, the deadzone simplifies to `(x − dz) / (1 − dz)`.
    This is the positive branch with `sign(x) = 1`. -/
theorem deadzone_pos_eq (x dz : Rat) (hxdz : dz < x) (hdz0 : 0 ≤ dz) :
    deadzone x dz = (x - dz) / (1 - dz) := by
  simp only [deadzone]
  have hx0 : 0 ≤ x := Rat.le_trans hdz0 (Rat.le_of_lt hxdz)
  have habs : dz < x.abs := by
    rw [Rat.abs_of_nonneg hx0]; exact hxdz
  rw [if_pos habs, signR_of_nonneg x hx0, Rat.one_mul]

/-- When `x < −dz ≤ 0`, the deadzone simplifies to `(x + dz) / (1 − dz)`.
    This is the negative branch with `sign(x) = −1`.

    Note: `x - (-1)*dz = x + dz` requires basic ring arithmetic over `Rat`.
    This algebra is proved below; it does NOT need Mathlib. -/
theorem deadzone_neg_eq (x dz : Rat) (hxdz : x < -dz) (hdz0 : 0 ≤ dz) :
    deadzone x dz = (x + dz) / (1 - dz) := by
  simp only [deadzone]
  have hxneg : x < 0 :=
    Std.lt_of_lt_of_le hxdz (Rat.neg_le_iff.mp hdz0)
  -- |x| = -x  (since x < 0)
  have habs_eq : x.abs = -x := Rat.abs_of_nonpos (Rat.le_of_lt hxneg)
  -- |-x| > dz (since x < -dz means -x > dz)
  have habs : dz < x.abs := by
    rw [habs_eq]
    exact Rat.neg_lt_neg_iff.mp (by rw [Rat.neg_neg]; exact hxdz)
  rw [if_pos habs, signR_of_neg x hxneg]
  -- x - (-1) * dz = x + dz
  congr 1
  rw [Rat.neg_mul, Rat.one_mul, Rat.sub_eq_add_neg, Rat.neg_neg]

/-! ## Sign of the output -/

/-- When `x > dz ≥ 0` and `dz < 1`, the output is positive. -/
theorem deadzone_pos (x dz : Rat) (hxdz : dz < x) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    0 < deadzone x dz := by
  rw [deadzone_pos_eq x dz hxdz hdz0]
  have hnum : 0 < x - dz := (Rat.lt_iff_sub_pos dz x).mp hxdz
  have hden : 0 < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  rw [Rat.div_def]
  exact Rat.mul_pos hnum (Rat.inv_pos.mpr hden)

/-- When `x < -dz ≤ 0` and `dz < 1`, the output is negative. -/
theorem deadzone_neg (x dz : Rat) (hxdz : x < -dz) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone x dz < 0 := by
  rw [deadzone_neg_eq x dz hxdz hdz0]
  -- Need: x + dz < 0, which follows from x < -dz
  -- Requires Rat arithmetic: x < -dz ↔ x + dz < 0
  -- TODO: (Mathlib: linarith closes this)
  have hnum : x + dz < 0 := by
    have key : x + dz < -dz + dz := (Rat.add_lt_add_right).mpr hxdz
    rw [Rat.add_comm (-dz) dz, ← Rat.sub_eq_add_neg, Rat.sub_self] at key
    exact key
  have hden : 0 < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  rw [Rat.div_def]
  exact (Rat.mul_neg_iff_of_pos_right (Rat.inv_pos.mpr hden)).mpr hnum

/-! ## Output range -/

/-- Upper bound: deadzone output is at most 1 when input is at most 1.

    The positive case is fully proved.
    The negative case uses `sorry` (needs Rat arithmetic; provable with Mathlib's `linarith`). -/
theorem deadzone_le_one (x dz : Rat) (hx1 : x ≤ 1) (_hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone x dz ≤ 1 := by
  simp only [deadzone]
  split
  · rename_i h
    have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
    by_cases hx0 : 0 ≤ x
    · -- Positive branch: (x - dz) / (1 - dz) ≤ 1 because x ≤ 1
      rw [signR_of_nonneg x hx0, Rat.one_mul]
      have h2 : x - dz ≤ 1 - dz := by
        rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
        exact (Rat.add_le_add_right).mpr hx1
      rw [Rat.div_def]
      calc (x - dz) * (1 - dz)⁻¹
          ≤ (1 - dz) * (1 - dz)⁻¹ :=
            Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt (Rat.inv_pos.mpr h1))
        _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)
    · -- Negative branch: x < 0, so output (x + dz)/(1 − dz) < 0 ≤ 1
      have hxneg : x < 0 := Rat.not_le.mp hx0
      -- |x| = −x since x < 0
      have habs : x.abs = -x := Rat.abs_of_nonpos (Rat.le_of_lt hxneg)
      -- dz < −x (from |x| > dz)
      have h' : dz < -x := habs ▸ h
      -- x < −dz (negate both sides of dz < −x)
      have hxdz : x < -dz :=
        Rat.neg_lt_neg_iff.mp (by rw [Rat.neg_neg]; exact h')
      rw [signR_of_neg x hxneg, Rat.neg_mul, Rat.one_mul,
          Rat.sub_eq_add_neg, Rat.neg_neg]
      -- Goal: (x + dz) / (1 − dz) ≤ 1. Show x + dz < 0 first.
      have hxpdz : x + dz < 0 := by
        have key : x + dz < -dz + dz := (Rat.add_lt_add_right).mpr hxdz
        rw [Rat.add_comm (-dz) dz, ← Rat.sub_eq_add_neg, Rat.sub_self] at key
        exact key
      apply Rat.le_of_lt
      apply Std.lt_trans _ (by decide : (0 : Rat) < 1)
      rw [Rat.div_def]
      exact (Rat.mul_neg_iff_of_pos_right (Rat.inv_pos.mpr h1)).mpr hxpdz
  · -- In deadzone: output = 0 ≤ 1
    exact Rat.le_of_lt (by decide)

/-- Lower bound: deadzone output is at least −1 when input is at least −1.

    Cases:
    - In deadzone: output = 0 ≥ −1.
    - Positive branch (x > dz ≥ 0): output > 0 ≥ −1.
    - Negative branch (x < −dz ≤ 0): output = (x+dz)/(1−dz).
      Since x ≥ −1, we have x+dz ≥ −1+dz = −(1−dz),
      so output ≥ −(1−dz)/(1−dz) = −1. -/
theorem deadzone_ge_neg_one (x dz : Rat) (hxm1 : -1 ≤ x) (_hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    -1 ≤ deadzone x dz := by
  simp only [deadzone]
  split
  · rename_i h
    have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
    by_cases hx0 : 0 ≤ x
    · -- Positive branch: output > 0 ≥ −1
      rw [signR_of_nonneg x hx0, Rat.one_mul]
      apply Rat.le_of_lt
      apply Std.lt_trans (by decide : (-1 : Rat) < 0)
      have hxabs : x.abs = x := Rat.abs_of_nonneg hx0
      have hnum : 0 < x - dz := (Rat.lt_iff_sub_pos dz x).mp (hxabs ▸ h)
      rw [Rat.div_def]
      exact Rat.mul_pos hnum (Rat.inv_pos.mpr h1)
    · -- Negative branch: −(1−dz) ≤ x+dz, so −1 ≤ (x+dz)/(1−dz)
      have hxneg : x < 0 := Rat.not_le.mp hx0
      rw [signR_of_neg x hxneg, Rat.neg_mul, Rat.one_mul,
          Rat.sub_eq_add_neg, Rat.neg_neg]
      -- −(1−dz) ≤ x+dz  because −1 ≤ x → −1+dz ≤ x+dz = −(1−dz) ≤ x+dz
      have hlower : -(1 - dz) ≤ x + dz := by
        rw [show -(1 - dz) = (-1 : Rat) + dz from by
          rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]]
        exact (Rat.add_le_add_right).mpr hxm1
      rw [Rat.div_def]
      calc (-1 : Rat)
          = -(1 - dz) * (1 - dz)⁻¹ := by
            rw [Rat.neg_mul, Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)]
        _ ≤ (x + dz) * (1 - dz)⁻¹ :=
            Rat.mul_le_mul_of_nonneg_right hlower (Rat.le_of_lt (Rat.inv_pos.mpr h1))
  · -- In deadzone: output = 0 ≥ −1
    exact Rat.le_of_lt (by decide)

/-! ## Special cases -/

/-- When there is no deadzone (`dz = 0`), the function is the identity on positives. -/
theorem deadzone_no_dz_pos (x : Rat) (hx : 0 < x) : deadzone x 0 = x := by
  rw [deadzone_pos_eq x 0 hx (Rat.le_refl)]
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
      Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
      Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]

/-- At maximum input (`x = 1`), output equals 1 for any `dz < 1`.

    Proof: `(1 - dz) / (1 - dz) = 1`. -/
theorem deadzone_at_max (dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone 1 dz = 1 := by
  rw [deadzone_pos_eq 1 dz hdz1 hdz0]
  -- Goal: (1 - dz) / (1 - dz) = 1
  have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)

/-- At minimum input (`x = -1`), output equals −1 for any `dz < 1`.

    Proof: `(-1 + dz) = -(1 - dz)`, so `(-1 + dz) / (1 - dz) = -1`. -/
theorem deadzone_at_min (dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone (-1) dz = -1 := by
  have hneg : (-1 : Rat) < -dz := by
    rw [Rat.neg_lt_neg_iff]; exact hdz1
  rw [deadzone_neg_eq (-1) dz hneg hdz0]
  have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  have h1ne : (1 - dz) ≠ 0 := Rat.ne_of_gt h1
  rw [show (-1 : Rat) + dz = -(1 - dz) from by
    rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]]
  rw [Rat.div_def, Rat.neg_mul, Rat.mul_inv_cancel _ h1ne]

/-! ## Odd symmetry -/

/-- **Odd symmetry**: the deadzone function is an odd function for `dz ≥ 0`.

    `deadzone (-x) dz = -(deadzone x dz)` — negating the input negates the output.
    This is a key structural property: the RC stick deadzone preserves sign symmetry. -/
theorem deadzone_odd (x dz : Rat) (hdz : 0 ≤ dz) :
    deadzone (-x) dz = -(deadzone x dz) := by
  by_cases h1 : dz < x
  · -- Case: x > dz (positive branch for x; negative branch for -x)
    have hneg : -x < -dz := Rat.neg_lt_neg h1
    rw [deadzone_pos_eq x dz h1 hdz, deadzone_neg_eq (-x) dz hneg hdz,
        Rat.div_def, Rat.div_def]
    have hfact : -((x - dz) * (1 - dz)⁻¹) = (-(x - dz)) * (1 - dz)⁻¹ := by
      rw [← Rat.neg_mul]
    rw [hfact]; congr 1
    rw [Rat.neg_sub x dz, Rat.sub_eq_add_neg]
    exact (Rat.add_comm dz (-x)).symm
  · by_cases h2 : x < -dz
    · -- Case: x < -dz (negative branch for x; positive branch for -x)
      have hpos : dz < -x := by have := Rat.neg_lt_neg h2; rwa [Rat.neg_neg] at this
      rw [deadzone_neg_eq x dz h2 hdz, deadzone_pos_eq (-x) dz hpos hdz,
          Rat.div_def, Rat.div_def]
      have hfact : -((x + dz) * (1 - dz)⁻¹) = (-(x + dz)) * (1 - dz)⁻¹ := by
        rw [← Rat.neg_mul]
      rw [hfact]; congr 1
      rw [Rat.neg_add, Rat.sub_eq_add_neg]
    · -- Case: |x| ≤ dz (both x and -x in the deadzone)
      have hin : x.abs ≤ dz := by
        have hhi := Rat.not_lt.mp h1
        have hlo := Rat.not_lt.mp h2
        by_cases hx0 : 0 ≤ x
        · rw [Rat.abs_of_nonneg hx0]; exact hhi
        · rw [Rat.abs_of_nonpos (Rat.le_of_lt (Rat.not_le.mp hx0))]
          exact Rat.neg_le_iff.mpr hlo
      rw [deadzone_in_dz x dz hin, deadzone_in_dz (-x) dz (by rwa [Rat.abs_neg]),
          Rat.neg_zero]

/-! ## Monotonicity -/

-- Private helpers used only by `deadzone_mono_val`
private theorem dz_le_abs (v : Rat) : v ≤ v.abs := by
  by_cases h : 0 ≤ v
  · rw [Rat.abs_of_nonneg h]; exact @Rat.le_refl v
  · exact Rat.le_trans (Rat.le_of_lt (Rat.not_le.mp h)) Rat.abs_nonneg

private theorem dz_neg_abs_le (v : Rat) : -v.abs ≤ v := by
  by_cases h : 0 ≤ v
  · rw [Rat.abs_of_nonneg h]; exact Rat.le_trans (Rat.neg_le_iff.mpr h) h
  · have hv : v < 0 := Rat.not_le.mp h
    rw [Rat.abs_of_nonpos (Rat.le_of_lt hv), Rat.neg_neg]; exact @Rat.le_refl v

private theorem dz_abs_le_left (v dz : Rat) (h : v.abs ≤ dz) : -dz ≤ v :=
  Rat.le_trans (Rat.neg_le_neg h) (dz_neg_abs_le v)

private theorem dz_one_sub_pos (dz : Rat) (h : dz < 1) : (0 : Rat) < 1 - dz := by
  have := Rat.add_lt_add_right (a := dz) (b := 1) (c := -dz) |>.mpr h
  rwa [Rat.add_neg_cancel, ← Rat.sub_eq_add_neg] at this

private theorem dz_div_le (a b c : Rat) (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr hc))

private theorem dz_sub_le (a b k : Rat) (h : a ≤ b) : a - k ≤ b - k := by
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]; exact (Rat.add_le_add_right (c := -k)).mpr h

private theorem dz_abs_out_neg (x dz : Rat) (hxneg : x < 0) (hxabs : x.abs > dz) : x < -dz := by
  rw [Rat.abs_of_nonpos (Rat.le_of_lt hxneg)] at hxabs
  have h := Rat.neg_lt_neg hxabs; rwa [Rat.neg_neg] at h

/-- **Monotonicity in the input value**: `deadzone` is non-decreasing in `v`.

    If `v₁ ≤ v₂` then `deadzone v₁ dz ≤ deadzone v₂ dz`.

    This is a key correctness property for RC stick processing: a larger stick
    deflection always produces a larger (or equal) output, preserving the
    direction of input changes across the deadzone boundary. -/
theorem deadzone_mono_val (v1 v2 dz : Rat) (hv : v1 ≤ v2) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone v1 dz ≤ deadzone v2 dz := by
  have h1mdz : (0 : Rat) < 1 - dz := dz_one_sub_pos dz hdz1
  by_cases h1 : v1.abs > dz
  · -- v1 outside deadzone
    by_cases h2 : v2.abs > dz
    · -- Both outside: monotone on each branch, or neg→pos gives neg<0<pos
      by_cases hv1pos : (0 : Rat) ≤ v1
      · -- Both positive (v1 ≤ v2, v1 ≥ 0 → v2 ≥ 0)
        have hv2pos : (0 : Rat) ≤ v2 := Rat.le_trans hv1pos hv
        rw [deadzone_pos_eq v1 dz (by rwa [Rat.abs_of_nonneg hv1pos] at h1) hdz0,
            deadzone_pos_eq v2 dz (by rwa [Rat.abs_of_nonneg hv2pos] at h2) hdz0]
        exact dz_div_le _ _ _ (dz_sub_le v1 v2 dz hv) h1mdz
      · -- v1 negative
        have hv1neg : v1 < 0 := Rat.not_le.mp hv1pos
        have hv1dz : v1 < -dz := dz_abs_out_neg v1 dz hv1neg h1
        by_cases hv2pos : (0 : Rat) ≤ v2
        · -- v1 negative, v2 non-negative
          have hv2dz : dz < v2 := by rwa [Rat.abs_of_nonneg hv2pos] at h2
          exact Rat.le_of_lt (Std.lt_trans (deadzone_neg v1 dz hv1dz hdz0 hdz1)
                                           (deadzone_pos v2 dz hv2dz hdz0 hdz1))
        · -- Both negative
          have hv2neg : v2 < 0 := Rat.not_le.mp hv2pos
          have hv2dz : v2 < -dz := dz_abs_out_neg v2 dz hv2neg h2
          rw [deadzone_neg_eq v1 dz hv1dz hdz0, deadzone_neg_eq v2 dz hv2dz hdz0]
          exact dz_div_le _ _ _ ((Rat.add_le_add_right (c := dz)).mpr hv) h1mdz
    · -- v1 outside, v2 inside: v1 must be negative (since v1 ≤ v2 ≤ dz < |v1|)
      have hin2 : v2.abs ≤ dz := Rat.not_lt.mp h2
      have hv1neg : v1 < 0 := by
        apply Classical.byContradiction; intro hv1pos
        have hv1nn : 0 ≤ v1 := Rat.not_lt.mp hv1pos
        rw [Rat.abs_of_nonneg hv1nn] at h1
        exact absurd (Rat.le_trans hv (Rat.le_trans (dz_le_abs v2) hin2)) (Rat.not_le.mpr h1)
      have hv1dz : v1 < -dz := dz_abs_out_neg v1 dz hv1neg h1
      rw [deadzone_in_dz v2 dz hin2]
      exact Rat.le_of_lt (deadzone_neg v1 dz hv1dz hdz0 hdz1)
  · -- v1 inside deadzone
    have hin1 : v1.abs ≤ dz := Rat.not_lt.mp h1
    rw [deadzone_in_dz v1 dz hin1]
    by_cases h2 : v2.abs > dz
    · -- v2 outside: v2 ≥ v1 ≥ -dz, so v2 must be positive (cannot be < -dz)
      have hv2dz : dz < v2 := by
        apply Classical.byContradiction; intro hv2neg_dz
        have hv2nn : ¬(0 ≤ v2) := fun hv2nn =>
          absurd (by rwa [Rat.abs_of_nonneg hv2nn] at h2) hv2neg_dz
        exact absurd (Rat.le_trans (dz_abs_le_left v1 dz hin1) hv)
                     (Rat.not_le.mpr (dz_abs_out_neg v2 dz (Rat.not_le.mp hv2nn) h2))
      exact Rat.le_of_lt (deadzone_pos v2 dz hv2dz hdz0 hdz1)
    · -- Both inside: 0 ≤ 0
      rw [deadzone_in_dz v2 dz (Rat.not_lt.mp h2)]; exact Rat.le_refl

/-! ## No-deadzone identity (general) -/

/-- The negative case of the no-deadzone identity: when `dz = 0`, `deadzone x 0 = x` for `x < 0`. -/
theorem deadzone_no_dz_neg (x : Rat) (hx : x < 0) : deadzone x 0 = x := by
  rw [deadzone_neg_eq x 0 (by rw [Rat.neg_zero]; exact hx) (Rat.le_refl)]
  rw [Rat.add_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
      Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]

/-- **Identity with no deadzone** (all cases): when `dz = 0`, `deadzone x 0 = x` for all `x`.

    Combining `deadzone_no_dz_pos`, `deadzone_no_dz_neg`, and the zero case (which is in the
    deadzone since `|0| = 0 = dz`), we get the full identity. -/
theorem deadzone_no_dz (x : Rat) : deadzone x 0 = x := by
  by_cases h1 : 0 < x
  · exact deadzone_no_dz_pos x h1
  · by_cases h2 : x = 0
    · subst h2
      simp [deadzone]
    · exact deadzone_no_dz_neg x (Rat.lt_of_le_of_ne (Rat.not_lt.mp h1) h2)

/-! ## Monotonicity in the deadzone width -/

-- Private helpers for `deadzone_mono_dz_pos`

/-- Inverse anti-monotonicity: larger positive denominators give smaller inverses. -/
private theorem dz_inv_anti (a b : Rat) (hba : b ≤ a) (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ := by
  have ha_ne : a ≠ 0 := Rat.ne_of_gt ha
  have hb_ne : b ≠ 0 := Rat.ne_of_gt hb
  rw [Rat.le_iff_sub_nonneg]
  have key : b⁻¹ - a⁻¹ = (a - b) * (a⁻¹ * b⁻¹) := by
    simp only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]
    rw [show a * (a⁻¹ * b⁻¹) = b⁻¹ by
          rw [← Rat.mul_assoc a a⁻¹ b⁻¹, Rat.mul_inv_cancel a ha_ne, Rat.one_mul]]
    rw [show b * (a⁻¹ * b⁻¹) = a⁻¹ by
          rw [Rat.mul_comm a⁻¹ b⁻¹, ← Rat.mul_assoc b b⁻¹ a⁻¹,
              Rat.mul_inv_cancel b hb_ne, Rat.one_mul]]
  rw [key]
  exact Rat.mul_nonneg ((Rat.le_iff_sub_nonneg b a).mp hba)
    (Rat.mul_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr ha)) (Rat.le_of_lt (Rat.inv_pos.mpr hb)))

/-- Rewrite `(x - dz) / (1 - dz)` as `1 - (1 - x) / (1 - dz)`. -/
private theorem dz_div_rewrite (x dz : Rat) (h1mdz : 0 < 1 - dz) :
    (x - dz) / (1 - dz) = 1 - (1 - x) / (1 - dz) := by
  rw [Rat.div_def, Rat.div_def]
  have h1mdz_ne : (1 - dz) ≠ 0 := Rat.ne_of_gt h1mdz
  have hn : (1 - dz) - (1 - x) = x - dz := by
    simp only [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
    rw [Rat.add_assoc, ← Rat.add_assoc (-dz) (-1) x, Rat.add_comm (-dz) (-1),
        Rat.add_assoc (-1) (-dz) x, ← Rat.add_assoc 1 (-1) (-dz + x),
        show (1:Rat) + -1 = 0 from Rat.add_neg_cancel 1, Rat.zero_add, Rat.add_comm (-dz) x]
  rw [show (x - dz) * (1 - dz)⁻¹ = ((1 - dz) - (1 - x)) * (1 - dz)⁻¹ from by rw [hn]]
  rw [show ((1 - dz) - (1 - x)) * (1 - dz)⁻¹ = (1 - dz) * (1 - dz)⁻¹ - (1 - x) * (1 - dz)⁻¹
      from by simp only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]]
  rw [Rat.mul_inv_cancel _ h1mdz_ne]

/-- `c - b ≤ c - a` when `a ≤ b`. -/
private theorem dz_sub_le_sub_l (a b c : Rat) (h : a ≤ b) : c - b ≤ c - a := by
  rw [Rat.le_iff_sub_nonneg (c - b) (c - a)]
  have key : (c - a) - (c - b) = b - a := by
    simp only [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
    rw [Rat.add_assoc c (-a) (-c + b), ← Rat.add_assoc (-a) (-c) b, Rat.add_comm (-a) (-c),
        Rat.add_assoc (-c) (-a) b, ← Rat.add_assoc c (-c) (-a + b),
        show c + -c = (0:Rat) from Rat.add_neg_cancel c, Rat.zero_add, Rat.add_comm (-a) b]
  rw [key]; exact (Rat.le_iff_sub_nonneg a b).mp h

/-- **Monotonicity in `dz`** (positive branch): for a fixed input `x`,
    increasing the deadzone width `dz` weakly decreases the output.

    Statement: `dz₁ ≤ dz₂ < x ≤ 1`, `0 ≤ dz₁`, `dz₂ < 1` →
    `deadzone x dz₂ ≤ deadzone x dz₁`.

    Proof: rewrite `(x - dz) / (1 - dz) = 1 - (1 - x) / (1 - dz)`. Since `dz₁ ≤ dz₂`,
    we have `1 - dz₂ ≤ 1 - dz₁`, so `(1 - dz₁)⁻¹ ≤ (1 - dz₂)⁻¹` by inverse anti-monotonicity.
    Multiplying by `1 - x ≥ 0` gives `(1 - x)/(1 - dz₁) ≤ (1 - x)/(1 - dz₂)`, hence the
    subtraction from 1 reverses the inequality. -/
theorem deadzone_mono_dz_pos (x dz1 dz2 : Rat)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (h12 : dz1 ≤ dz2) (hdz0 : 0 ≤ dz1) (hdz1 : dz2 < 1) (hout : dz2 < x) :
    deadzone x dz2 ≤ deadzone x dz1 := by
  have hout1 : dz1 < x := Std.lt_of_le_of_lt h12 hout
  rw [deadzone_pos_eq x dz1 hout1 hdz0,
      deadzone_pos_eq x dz2 hout (Rat.le_trans hdz0 h12)]
  have hd1 : (0:Rat) < 1 - dz1 := dz_one_sub_pos dz1 (Std.lt_of_le_of_lt h12 hdz1)
  have hd2 : (0:Rat) < 1 - dz2 := dz_one_sub_pos dz2 hdz1
  -- Rewrite both sides: (x - dz) / (1 - dz) = 1 - (1 - x) / (1 - dz)
  rw [dz_div_rewrite x dz1 hd1, dz_div_rewrite x dz2 hd2]
  -- Goal: 1 - (1 - x) / (1 - dz2) ≤ 1 - (1 - x) / (1 - dz1)
  apply dz_sub_le_sub_l
  -- Goal: (1 - x) / (1 - dz1) ≤ (1 - x) / (1 - dz2)
  rw [Rat.div_def, Rat.div_def]
  have h1mx : (0:Rat) ≤ 1 - x := (Rat.le_iff_sub_nonneg x 1).mp hx1
  -- 1 - dz2 ≤ 1 - dz1 (because dz1 ≤ dz2)
  have hdz12 : (1:Rat) - dz2 ≤ 1 - dz1 := by
    rw [Rat.le_iff_sub_nonneg]
    have key : (1 - dz1) - (1 - dz2) = dz2 - dz1 := by
      simp only [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
      rw [Rat.add_assoc 1 (-dz1) (-1 + dz2), ← Rat.add_assoc (-dz1) (-1) dz2,
          Rat.add_comm (-dz1) (-1), Rat.add_assoc (-1) (-dz1) dz2,
          ← Rat.add_assoc 1 (-1) (-dz1 + dz2),
          show (1:Rat) + -1 = 0 from Rat.add_neg_cancel 1,
          Rat.zero_add, Rat.add_comm (-dz1) dz2]
    rw [key]; exact (Rat.le_iff_sub_nonneg dz1 dz2).mp h12
  -- (1 - dz1)⁻¹ ≤ (1 - dz2)⁻¹ by inverse anti-monotonicity
  have hinv : (1 - dz1)⁻¹ ≤ (1 - dz2)⁻¹ := dz_inv_anti (1 - dz1) (1 - dz2) hdz12 hd1 hd2
  exact Rat.mul_le_mul_of_nonneg_left hinv h1mx

/-! ## Summary of proved properties

  | Theorem                 | Statement                                             | Status  |
  |-------------------------|-------------------------------------------------------|---------|
  | `deadzone_in_dz`        | `|x| ≤ dz → deadzone x dz = 0`                       | ✅ Proved |
  | `signR_of_nonneg`       | `x ≥ 0 → signR x = 1`                                | ✅ Proved |
  | `signR_of_neg`          | `x < 0 → signR x = −1`                               | ✅ Proved |
  | `deadzone_pos_eq`       | Simplified form for positive branch                   | ✅ Proved |
  | `deadzone_neg_eq`       | Simplified form for negative branch                   | ✅ Proved |
  | `deadzone_pos`          | `x > dz ≥ 0, dz < 1 → deadzone x dz > 0`            | ✅ Proved |
  | `deadzone_neg`          | `x < -dz ≤ 0, dz < 1 → deadzone x dz < 0`           | ✅ Proved |
  | `deadzone_no_dz_pos`    | `deadzone x 0 = x` (identity, positive case)         | ✅ Proved |
  | `deadzone_no_dz_neg`    | `deadzone x 0 = x` (identity, negative case)         | ✅ Proved |
  | `deadzone_no_dz`        | `deadzone x 0 = x` (identity, all inputs)            | ✅ Proved |
  | `deadzone_at_max`       | `deadzone 1 dz = 1` (for `dz < 1`)                   | ✅ Proved |
  | `deadzone_at_min`       | `deadzone (-1) dz = -1` (for `dz < 1`)               | ✅ Proved |
  | `deadzone_le_one`       | `x ≤ 1, 0 ≤ dz < 1 → deadzone x dz ≤ 1`             | ✅ Proved |
  | `deadzone_ge_neg_one`   | `-1 ≤ x, 0 ≤ dz < 1 → -1 ≤ deadzone x dz`           | ✅ Proved |
  | `deadzone_odd`          | `dz ≥ 0 → deadzone (-x) dz = -(deadzone x dz)`       | ✅ Proved |
  | `deadzone_mono_val`     | `v₁ ≤ v₂ → deadzone v₁ dz ≤ deadzone v₂ dz`         | ✅ Proved |
  | `deadzone_mono_dz_pos`  | `dz₁ ≤ dz₂ < x ≤ 1 → deadzone x dz₂ ≤ deadzone x dz₁` | ✅ Proved |
-/

end PX4.Deadzone
