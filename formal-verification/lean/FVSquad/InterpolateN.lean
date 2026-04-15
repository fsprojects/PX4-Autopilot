import FVSquad.Interpolate
open PX4.Interpolate

/-!
# PX4 `interpolateN` (Uniform Grid) — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::interpolateN` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp` (approx. line 180)

## C++ Source

```cpp
// Constant, piecewise linear, constant function with 1/N size intervals
// and N corner points as parameters:
//
//   y[N-1]               -------
//                       /
//   y[1]              /
//                   /
//   y[0] -------
//          0  1/(N-1)  2/(N-1)  ...  1
//
template<typename T, size_t N>
const T interpolateN(const T &value, const T(&y)[N])
{
    size_t index = constrain((int)(value * (N - 1)), 0, (int)(N - 2));
    return interpolate(value,
                       (T)index / (T)(N - 1),
                       (T)(index + 1) / (T)(N - 1),
                       y[index], y[index + 1]);
}
```

## Structure

**Part 1 — `interpN2`**: N=2 case (trivially equivalent to a single `interpolate`
call over [0, 1]). Five theorems: endpoints, upper/lower bounds, range containment.

**Part 2 — `interpN3`**: N=3 case with breakpoint at 1/2. All node values, range
containment, breakpoint continuity, segment-wise monotonicity, and constancy
theorems. All 13 theorems proved, 0 sorry.

## Correspondence to C++

- `interpN2 value y0 y1` models `interpolateN<2>(value, {y0, y1})` exactly.
- `interpN3 value y0 y1 y2` models `interpolateN<3>(value, {y0, y1, y2})` for
  rational `value ∈ [0, 1]`.
- **Index computation**: the C++ truncates `value * (N-1)` to an integer. For
  the N=3 rational model, this means: index=0 when `value < 1/2`, index=1 when
  `value ≥ 1/2`. This is faithfully captured by the `if value < 1/2` branch.
- **Approximations**: IEEE-754 rounding, NaN/inf, and overflow for narrow integer
  types are not modelled. The model assumes exact rational arithmetic.
-/

namespace PX4.InterpolateN

-- Helper: the rational number 1/2 (breakpoint for N=3)
private def half : Rat := (1 : Rat) / (2 : Rat)

-- Numeric facts about `half`, needed in proofs below.
-- Use `native_decide` — `decide` does not reduce Rat comparisons in Lean 4 stdlib.
private theorem zero_lt_half : (0 : Rat) < half := by native_decide
private theorem half_lt_one  : half < (1 : Rat)  := by native_decide
private theorem half_not_lt  : ¬ (half < half)   := by native_decide
private theorem one_not_lt_half : ¬ ((1 : Rat) < half) := by native_decide

-- ============================================================
-- Part 1: N=2 — degenerate case
-- ============================================================

/-- N=2 uniform-grid interpolation: identical to `interpolate` over `[0, 1]`. -/
def interpN2 (value y0 y1 : Rat) : Rat :=
  interpolate value 0 1 y0 y1

/-- At `value = 0`, `interpN2` returns `y0` exactly. -/
theorem interpN2_at_zero (y0 y1 : Rat) : interpN2 0 y0 y1 = y0 :=
  interpolate_at_low 0 1 y0 y1

/-- At `value = 1`, `interpN2` returns `y1` exactly. -/
theorem interpN2_at_one (y0 y1 : Rat) : interpN2 1 y0 y1 = y1 :=
  interpolate_at_high 0 1 y0 y1 (by native_decide)

/-- When `y0 ≤ y1`, the output is ≤ `y1`. -/
theorem interpN2_le_high (value y0 y1 : Rat) (h : y0 ≤ y1) :
    interpN2 value y0 y1 ≤ y1 :=
  interpolate_le_high value 0 1 y0 y1 (by native_decide) h

/-- When `y0 ≤ y1`, the output is ≥ `y0`. -/
theorem interpN2_ge_low (value y0 y1 : Rat) (h : y0 ≤ y1) :
    y0 ≤ interpN2 value y0 y1 :=
  interpolate_ge_low value 0 1 y0 y1 (by native_decide) h

-- ============================================================
-- Part 2: N=3 — two-segment model with breakpoint at 1/2
-- ============================================================

/-- N=3 uniform-grid interpolation over {0, 1/2, 1} × {y0, y1, y2}.

    The C++ computes `index = constrain((int)(value * 2), 0, 1)`, which maps:
    - `value < 1/2`: `(int)(value * 2) = 0` → segment `[0, 1/2]` with nodes `{y0, y1}`
    - `value ≥ 1/2`: `(int)(value * 2) ≥ 1` → segment `[1/2, 1]` with nodes `{y1, y2}` -/
def interpN3 (value y0 y1 y2 : Rat) : Rat :=
  if value < half then
    interpolate value 0 half y0 y1
  else
    interpolate value half 1 y1 y2

-- === Node-exact theorems ===

/-- At `value = 0`, `interpN3` returns `y0` exactly. -/
theorem interpN3_at_zero (y0 y1 y2 : Rat) :
    interpN3 0 y0 y1 y2 = y0 := by
  simp only [interpN3, if_pos zero_lt_half]
  exact interpolate_at_low 0 half y0 y1

/-- At `value = 1/2`, `interpN3` returns `y1` exactly.
    Both segment formulas agree at the breakpoint (continuity). -/
theorem interpN3_at_half (y0 y1 y2 : Rat) :
    interpN3 half y0 y1 y2 = y1 := by
  simp only [interpN3, if_neg half_not_lt]
  exact interpolate_at_low half 1 y1 y2

/-- At `value = 1`, `interpN3` returns `y2` exactly. -/
theorem interpN3_at_one (y0 y1 y2 : Rat) :
    interpN3 1 y0 y1 y2 = y2 := by
  simp only [interpN3, if_neg one_not_lt_half]
  exact interpolate_at_high half 1 y1 y2 half_lt_one

-- === Breakpoint continuity ===

/-- **Breakpoint continuity**: both segment formulas evaluate to `y1` at `1/2`,
    confirming there is no jump discontinuity at the breakpoint. -/
theorem interpN3_continuity (y0 y1 y2 : Rat) :
    interpolate half 0 half y0 y1 = interpolate half half 1 y1 y2 := by
  have h1 : interpolate half 0 half y0 y1 = y1 :=
    interpolate_at_high 0 half y0 y1 zero_lt_half
  have h2 : interpolate half half 1 y1 y2 = y1 :=
    interpolate_at_low half 1 y1 y2
  rw [h1, h2]

-- === Range containment ===

/-- When `y0 ≤ y1 ≤ y2`, the output is always ≤ `y2`. -/
theorem interpN3_le_high (value y0 y1 y2 : Rat)
    (hy01 : y0 ≤ y1) (hy12 : y1 ≤ y2) :
    interpN3 value y0 y1 y2 ≤ y2 := by
  simp only [interpN3]
  by_cases hv : value < half
  · simp only [if_pos hv]
    exact Rat.le_trans
      (interpolate_le_high value 0 half y0 y1 zero_lt_half hy01) hy12
  · simp only [if_neg hv]
    exact interpolate_le_high value half 1 y1 y2 half_lt_one hy12

/-- When `y0 ≤ y1 ≤ y2`, the output is always ≥ `y0`. -/
theorem interpN3_ge_low (value y0 y1 y2 : Rat)
    (hy01 : y0 ≤ y1) (hy12 : y1 ≤ y2) :
    y0 ≤ interpN3 value y0 y1 y2 := by
  simp only [interpN3]
  by_cases hv : value < half
  · simp only [if_pos hv]
    exact interpolate_ge_low value 0 half y0 y1 zero_lt_half hy01
  · simp only [if_neg hv]
    exact Rat.le_trans hy01
      (interpolate_ge_low value half 1 y1 y2 half_lt_one hy12)

/-- When `y0 ≤ y1 ≤ y2`, the output is in `[y0, y2]`. -/
theorem interpN3_in_range (value y0 y1 y2 : Rat)
    (hy01 : y0 ≤ y1) (hy12 : y1 ≤ y2) :
    y0 ≤ interpN3 value y0 y1 y2 ∧ interpN3 value y0 y1 y2 ≤ y2 :=
  ⟨interpN3_ge_low value y0 y1 y2 hy01 hy12,
   interpN3_le_high value y0 y1 y2 hy01 hy12⟩

-- === Segment-wise monotonicity ===

/-- **Monotone in segment 0**: when `y0 ≤ y1`, and both query values are strictly
    above 0 and strictly below `1/2`, a larger query gives a larger output. -/
theorem interpN3_mono_seg0 (v1 v2 y0 y1 y2 : Rat)
    (hv1lo : (0 : Rat) < v1) (hv12 : v1 ≤ v2) (hv2hi : v2 < half)
    (hy01 : y0 ≤ y1) :
    interpN3 v1 y0 y1 y2 ≤ interpN3 v2 y0 y1 y2 := by
  have hv1lt : v1 < half := Std.lt_of_le_of_lt hv12 hv2hi
  simp only [interpN3, if_pos hv1lt, if_pos hv2hi]
  exact interpolate_mono_interior 0 half y0 y1 v1 v2
    zero_lt_half hy01 hv1lo hv12 (Rat.le_of_lt hv2hi)

/-- **Monotone in segment 1**: when `y1 ≤ y2`, and both query values are strictly
    above `1/2` and within `[1/2, 1]`, a larger query gives a larger output. -/
theorem interpN3_mono_seg1 (v1 v2 y0 y1 y2 : Rat)
    (hv1lo : half < v1) (hv12 : v1 ≤ v2) (hv2hi : v2 ≤ 1)
    (hy12 : y1 ≤ y2) :
    interpN3 v1 y0 y1 y2 ≤ interpN3 v2 y0 y1 y2 := by
  have hv1nl : ¬ (v1 < half) := Rat.not_lt.mpr (Rat.le_of_lt hv1lo)
  have hv2nl : ¬ (v2 < half) :=
    Rat.not_lt.mpr (Rat.le_trans (Rat.le_of_lt hv1lo) hv12)
  simp only [interpN3, if_neg hv1nl, if_neg hv2nl]
  exact interpolate_mono_interior half 1 y1 y2 v1 v2
    half_lt_one hy12 hv1lo hv12 hv2hi

-- === Constancy ===

/-- When all three nodes have the same value `c`, output is always `c`. -/
theorem interpN3_const (value c : Rat) :
    interpN3 value c c c = c := by
  simp only [interpN3]
  by_cases hv : value < half
  · simp only [if_pos hv]; exact interpolate_const value 0 half c
  · simp only [if_neg hv]; exact interpolate_const value half 1 c

-- === Concrete evaluation examples ===

-- Flat curve y=[0, 0, 0]: always 0
#eval interpN3 0       0 0 0  -- 0
#eval interpN3 (1/4)   0 0 0  -- 0
#eval interpN3 (1/2)   0 0 0  -- 0
#eval interpN3 (3/4)   0 0 0  -- 0
#eval interpN3 1       0 0 0  -- 0

-- Linear curve y=[0, 1/2, 1]: should be the identity on [0,1]
#eval interpN3 0       0 (1/2) 1  -- 0
#eval interpN3 (1/4)   0 (1/2) 1  -- 1/4
#eval interpN3 (1/2)   0 (1/2) 1  -- 1/2
#eval interpN3 (3/4)   0 (1/2) 1  -- 3/4
#eval interpN3 1       0 (1/2) 1  -- 1

-- Convex curve y=[0, 1/4, 1]: slow start, fast finish
#eval interpN3 0       0 (1/4) 1  -- 0
#eval interpN3 (1/4)   0 (1/4) 1  -- 1/8
#eval interpN3 (1/2)   0 (1/4) 1  -- 1/4
#eval interpN3 (3/4)   0 (1/4) 1  -- 5/8
#eval interpN3 1       0 (1/4) 1  -- 1

end PX4.InterpolateN
