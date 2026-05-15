import Init.Data.Rat.Basic

/-!
# PX4 `BlockLimitSym` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of PX4's symmetric
clamp/saturation block `BlockLimitSym`:

- **C++ source**: `src/lib/controllib/BlockLimitSym.cpp` (lines 47–57) and
  `src/lib/controllib/BlockLimitSym.hpp` (lines 63–73)

## C++ Source

```cpp
float BlockLimitSym::update(float input)
{
    if (input > getMax()) {
        input = _max.get();
    } else if (input < -getMax()) {
        input = -getMax();
    }
    return input;
}
```

## Model

Over `Rat` (exact rational arithmetic), the pure functional model of `update` is:

```
limitSym(input, max) =
  if input > max  then  max
  if input < -max then  -max
  otherwise            input
```

**Abstracted away**: The `_max` parameter object, the `Block` hierarchy, and
floating-point rounding. The Lean model captures the pure numeric behaviour.
The C++ implementation assumes `max ≥ 0` (always the case in practice);
several theorems require this hypothesis.

## Properties Proved (10 theorems, 0 sorry)

1. `limitSym_above`       — input above max → output = max
2. `limitSym_below`       — input below −max → output = −max (requires max ≥ 0)
3. `limitSym_in_range`    — input in [−max, max] → output = input (pass-through)
4. `limitSym_upper`       — output ≤ max (requires max ≥ 0)
5. `limitSym_lower`       — −max ≤ output (requires max ≥ 0)
6. `limitSym_range`       — −max ≤ output ≤ max (combined, requires max ≥ 0)
7. `limitSym_idempotent`  — applying twice = applying once (requires max ≥ 0)
8. `limitSym_zero`        — limitSym 0 max = 0 when max ≥ 0
9. `limitSym_sym`         — limitSym (−x) max = −(limitSym x max) (odd function, requires max ≥ 0)
10. `limitSym_mono`       — monotone in input (requires max ≥ 0)
-/

namespace PX4.BlockLimitSym

def limitSym (input max : Rat) : Rat :=
  if input > max then max
  else if input < -max then -max
  else input

theorem limitSym_above (input max : Rat) (h : input > max) :
    limitSym input max = max := by
  unfold limitSym; rw [if_pos h]

theorem limitSym_below (input max : Rat) (hmax : 0 ≤ max) (h : input < -max) :
    limitSym input max = -max := by
  unfold limitSym
  rw [if_neg (Rat.not_lt.mpr (Rat.le_trans (Rat.le_of_lt h)
        (Rat.le_trans (Rat.neg_le_iff.mp hmax) hmax))),
      if_pos h]

theorem limitSym_in_range (input max : Rat) (h1 : -max ≤ input) (h2 : input ≤ max) :
    limitSym input max = input := by
  unfold limitSym
  rw [if_neg (Rat.not_lt.mpr h2), if_neg (Rat.not_lt.mpr h1)]

theorem limitSym_upper (input max : Rat) (hmax : 0 ≤ max) : limitSym input max ≤ max := by
  unfold limitSym
  by_cases h1 : input > max
  · rw [if_pos h1]; exact Rat.le_refl
  · by_cases h2 : input < -max
    · rw [if_neg h1, if_pos h2]; exact Rat.le_trans (Rat.neg_le_iff.mp hmax) hmax
    · rw [if_neg h1, if_neg h2]; exact Rat.not_lt.mp h1

theorem limitSym_lower (input max : Rat) (hmax : 0 ≤ max) : -max ≤ limitSym input max := by
  unfold limitSym
  by_cases h1 : input > max
  · rw [if_pos h1]; exact Rat.le_trans (Rat.neg_le_iff.mp hmax) hmax
  · by_cases h2 : input < -max
    · rw [if_neg h1, if_pos h2]; exact Rat.le_refl
    · rw [if_neg h1, if_neg h2]; exact Rat.not_lt.mp h2

theorem limitSym_range (input max : Rat) (hmax : 0 ≤ max) :
    -max ≤ limitSym input max ∧ limitSym input max ≤ max :=
  ⟨limitSym_lower input max hmax, limitSym_upper input max hmax⟩

theorem limitSym_idempotent (input max : Rat) (hmax : 0 ≤ max) :
    limitSym (limitSym input max) max = limitSym input max :=
  limitSym_in_range _ _ (limitSym_lower input max hmax) (limitSym_upper input max hmax)

theorem limitSym_zero (max : Rat) (hmax : 0 ≤ max) : limitSym 0 max = 0 :=
  limitSym_in_range 0 max (Rat.neg_le_iff.mp hmax) hmax

/-- `limitSym` is an odd function: `limitSym (-x) max = -(limitSym x max)`.

    The positive and negative saturation boundaries are symmetric about zero. -/
theorem limitSym_sym (x max : Rat) (hmax : 0 ≤ max) :
    limitSym (-x) max = -(limitSym x max) := by
  unfold limitSym
  by_cases h1 : x > max
  · have h2 : -x < -max := Rat.neg_lt_neg h1
    have hno : ¬ (-x) > max :=
      Rat.not_lt.mpr (Rat.le_trans (Rat.le_of_lt h2)
        (Rat.le_trans (Rat.neg_le_iff.mp hmax) hmax))
    rw [if_pos h1, if_neg hno, if_pos h2]
  · by_cases h2 : x < -max
    · have h3 : max < -x := by
        have := Rat.neg_lt_neg h2
        rw [show -(-max) = max from Rat.neg_neg max] at this; exact this
      rw [if_neg h1, if_pos h2, if_pos h3]
      exact (Rat.neg_neg max).symm
    · have hnx_hi : -x ≤ max := Rat.neg_le_iff.mpr (Rat.not_lt.mp h2)
      have hnx_lo : -max ≤ -x := Rat.neg_le_neg (Rat.not_lt.mp h1)
      rw [if_neg h1, if_neg h2,
          if_neg (Rat.not_lt.mpr hnx_hi), if_neg (Rat.not_lt.mpr hnx_lo)]

/-- `limitSym` is monotone in its input.

    Saturation is a non-decreasing operation: larger inputs produce outputs
    that are at least as large. -/
theorem limitSym_mono (a b max : Rat) (hmax : 0 ≤ max) (h : a ≤ b) :
    limitSym a max ≤ limitSym b max := by
  unfold limitSym
  by_cases ha1 : a > max
  · rw [if_pos ha1]
    by_cases hb1 : b > max
    · rw [if_pos hb1]; exact Rat.le_refl
    · exact absurd (Std.lt_of_lt_of_le ha1 h) hb1
  · by_cases ha2 : a < -max
    · rw [if_neg ha1, if_pos ha2]
      by_cases hb1 : b > max
      · rw [if_pos hb1]; exact Rat.le_trans (Rat.neg_le_iff.mp hmax) hmax
      · by_cases hb2 : b < -max
        · rw [if_neg hb1, if_pos hb2]; exact Rat.le_refl
        · rw [if_neg hb1, if_neg hb2]; exact Rat.not_lt.mp hb2
    · rw [if_neg ha1, if_neg ha2]
      by_cases hb1 : b > max
      · rw [if_pos hb1]; exact Rat.not_lt.mp ha1
      · by_cases hb2 : b < -max
        · exact absurd (Std.lt_of_lt_of_le hb2 (Rat.not_lt.mp ha2)) (Rat.not_lt.mpr h)
        · rw [if_neg hb1, if_neg hb2]; exact h

end PX4.BlockLimitSym
