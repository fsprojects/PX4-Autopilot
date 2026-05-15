/-!
# PX4 PurePursuit — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of the lookahead distance
computation in `PurePursuit::calcTargetBearing` from PX4-Autopilot's pure-pursuit
path tracking library.

- **C++ source**: `src/lib/pure_pursuit/PurePursuit.cpp`
- **Informal spec**: `formal-verification/specs/purepursuit_informal.md`
- **Reference**: Coulter (1992), *Implementation of the Pure Pursuit Path Tracking
  Algorithm*, CMU-RI-TR-92-01.

## What is modelled

The **lookahead distance computation** is modelled as a pure rational function:

```cpp
// From PurePursuit::calcTargetBearing
const float lookahead_distance = math::constrain(
    _lookahead_gain * fabsf(vehicle_speed),
    _npfg_period_min, _npfg_period_max);
```

We define `lookaheadDist gain speed lMin lMax` over `Rat` and prove:

1. **`lookahead_in_range`** — the primary safety property: lookahead is always in
   `[lMin, lMax]` when `lMin ≤ lMax`, regardless of gain or speed.
2. **`lookahead_at_zero_speed`** — at zero speed, lookahead = `lMin`.
3. **`lookahead_clamped_at_min`** — if `gain * |speed| < lMin`, result is `lMin`.
4. **`lookahead_at_lmin`** — if `gain * |speed| = lMin` (in range), result is `lMin`.
5. **`lookahead_clamped_at_max`** — if `gain * |speed| > lMax`, result is `lMax`.
6. **`lookahead_symmetric_speed`** — negating speed gives the same lookahead.
7. **`lookahead_mono_speed_abs`** — for non-negative gain, lookahead is non-decreasing
   in speed magnitude.
8. **`lookahead_inverted_bounds_high_speed`** — when `lMax < lMin` (misconfigured bounds)
   and speed is high (`gain * |speed| ≥ lMin`), the result is `lMax` (the smaller value)
   — a latent configuration hazard (open question 2 in the informal spec).
9. **`absRat_nonneg`** — `|x| ≥ 0`.
10. **`absRat_neg`** — `|-x| = |x|`.

## Approximations / out of scope

- **Float arithmetic**: all computations are modelled over `Rat` (exact arithmetic).
  No overflow, NaN, or ±∞.
- **Bearing geometry**: `atan2`, `sqrt`, `wrap_pi`, and 2D vector operations are
  NOT modelled. Only the lookahead distance computation is formalised.
- **`fabsf`**: modelled as `absRat`.
- **10 theorems, 0 sorry.**
-/

namespace PX4.PurePursuit

/-! ## Absolute value over Rat -/

/-- Absolute value over `Rat`. Models `fabsf(vehicle_speed)`. -/
def absRat (x : Rat) : Rat := if x < 0 then -x else x

/-- `absRat` is non-negative. -/
theorem absRat_nonneg (x : Rat) : 0 ≤ absRat x := by
  simp only [absRat]
  by_cases h : x < 0
  · simp only [if_pos h]
    have hlt : -0 < -x := Rat.neg_lt_neg h
    rw [Rat.neg_zero] at hlt
    exact Rat.le_of_lt hlt
  · simp only [if_neg h]
    exact Rat.not_lt.mp h

/-- `absRat` of a negation equals `absRat` of the original. -/
theorem absRat_neg (x : Rat) : absRat (-x) = absRat x := by
  simp only [absRat]
  by_cases h : x < 0
  · simp only [if_pos h]
    have hnx : ¬ -x < 0 := by
      intro hc
      have h1 : -0 < -x := Rat.neg_lt_neg h
      rw [Rat.neg_zero] at h1
      exact absurd hc (Rat.not_lt.mpr (Rat.le_of_lt h1))
    simp only [if_neg hnx]
  · simp only [if_neg h]
    by_cases h2 : -x < 0
    · simp only [if_pos h2]
      exact Rat.neg_neg x
    · simp only [if_neg h2]
      -- x ≥ 0 and -x ≥ 0 → x = 0
      have hx0 : 0 ≤ x := Rat.not_lt.mp h
      have hnx0 : 0 ≤ -x := Rat.not_lt.mp h2
      have hx_le : x ≤ 0 := by
        have := Rat.neg_le_neg hnx0
        rw [Rat.neg_neg, Rat.neg_zero] at this
        exact this
      have hx : x = 0 := Rat.le_antisymm hx_le hx0
      rw [hx]; exact Rat.neg_zero

/-! ## Rational constrain -/

/-- `constrainPP val lo hi` clamps `val` to `[lo, hi]`.
    Models `math::constrain` from `src/lib/mathlib/math/Limits.hpp`. -/
def constrainPP (val lo hi : Rat) : Rat :=
  if val < lo then lo
  else if val > hi then hi
  else val

private theorem constrainPP_ge_lo (val lo hi : Rat) (h : lo ≤ hi) :
    lo ≤ constrainPP val lo hi := by
  simp only [constrainPP]
  by_cases h1 : val < lo
  · simp only [if_pos h1]; exact Rat.le_refl
  · simp only [if_neg h1]
    by_cases h2 : val > hi
    · simp only [if_pos h2]; exact h
    · simp only [if_neg h2]; exact Rat.not_lt.mp h1

private theorem constrainPP_le_hi (val lo hi : Rat) (h : lo ≤ hi) :
    constrainPP val lo hi ≤ hi := by
  simp only [constrainPP]
  by_cases h1 : val < lo
  · simp only [if_pos h1]; exact h
  · simp only [if_neg h1]
    by_cases h2 : val > hi
    · simp only [if_pos h2]; exact Rat.le_refl
    · simp only [if_neg h2]; exact Rat.not_lt.mp h2

/-! ## Lookahead distance model -/

/-- `lookaheadDist gain speed lMin lMax` is the clamped lookahead distance.
    Models `math::constrain(_lookahead_gain * fabsf(vehicle_speed), lMin, lMax)`. -/
def lookaheadDist (gain speed lMin lMax : Rat) : Rat :=
  constrainPP (gain * absRat speed) lMin lMax

/-! ## Safety and correctness theorems -/

/-- **Safety theorem**: the lookahead distance is always in `[lMin, lMax]` when
    `lMin ≤ lMax`. The vehicle always uses a lookahead distance within the configured
    range, regardless of speed or gain. This prevents degenerate navigation (zero
    lookahead causes oscillation; unbounded lookahead causes aggressive corner-cutting). -/
theorem lookahead_in_range (gain speed lMin lMax : Rat) (h : lMin ≤ lMax) :
    lMin ≤ lookaheadDist gain speed lMin lMax ∧
    lookaheadDist gain speed lMin lMax ≤ lMax :=
  ⟨constrainPP_ge_lo _ lMin lMax h, constrainPP_le_hi _ lMin lMax h⟩

/-- At zero speed the lookahead is exactly `lMin` (when `0 ≤ lMin ≤ lMax`). -/
theorem lookahead_at_zero_speed (gain lMin lMax : Rat)
    (h : lMin ≤ lMax) (hlo : 0 ≤ lMin) :
    lookaheadDist gain 0 lMin lMax = lMin := by
  simp only [lookaheadDist, absRat, show ¬ (0:Rat) < 0 from Rat.lt_irrefl, if_false,
             Rat.mul_zero, constrainPP]
  by_cases h1 : (0 : Rat) < lMin
  · simp only [if_pos h1]
  · simp only [if_neg h1]
    have heq : lMin = 0 := Rat.le_antisymm (Rat.not_lt.mp h1) hlo
    subst heq
    simp only [show ¬ (0:Rat) > lMax from Rat.not_lt.mpr h, if_false]

/-- When the raw lookahead is below `lMin`, the result is `lMin`. -/
theorem lookahead_clamped_at_min (gain speed lMin lMax : Rat)
    (hclamp : gain * absRat speed < lMin) :
    lookaheadDist gain speed lMin lMax = lMin := by
  simp only [lookaheadDist, constrainPP, if_pos hclamp]

/-- When the raw lookahead equals `lMin`, the result is `lMin`. -/
theorem lookahead_at_lmin (gain speed lMin lMax : Rat) (h : lMin ≤ lMax)
    (hclamp : gain * absRat speed = lMin) :
    lookaheadDist gain speed lMin lMax = lMin := by
  simp only [lookaheadDist, constrainPP]
  rw [hclamp]
  simp only [show ¬ lMin < lMin from Rat.lt_irrefl, if_false,
             show ¬ lMin > lMax from Rat.not_lt.mpr h, if_false]

/-- When the raw lookahead exceeds `lMax`, the result is `lMax`. -/
theorem lookahead_clamped_at_max (gain speed lMin lMax : Rat) (h : lMin ≤ lMax)
    (hclamp : lMax < gain * absRat speed) :
    lookaheadDist gain speed lMin lMax = lMax := by
  simp only [lookaheadDist, constrainPP]
  have hge : ¬ (gain * absRat speed < lMin) := fun hlt =>
    absurd (Rat.le_trans h (Rat.le_of_lt hclamp)) (Rat.not_le.mpr hlt)
  simp only [if_neg hge, if_pos hclamp]

/-- Negating speed gives the same lookahead distance. -/
theorem lookahead_symmetric_speed (gain speed lMin lMax : Rat) :
    lookaheadDist gain speed lMin lMax = lookaheadDist gain (-speed) lMin lMax := by
  simp only [lookaheadDist, absRat_neg]

/-- For non-negative gain, lookahead is non-decreasing in speed magnitude.
    If `|speed1| ≤ |speed2|` and `0 ≤ gain`, then
    `lookaheadDist gain speed1 ≤ lookaheadDist gain speed2`. -/
theorem lookahead_mono_speed_abs (gain speed1 speed2 lMin lMax : Rat)
    (h : lMin ≤ lMax) (hg : 0 ≤ gain) (hs : absRat speed1 ≤ absRat speed2) :
    lookaheadDist gain speed1 lMin lMax ≤ lookaheadDist gain speed2 lMin lMax := by
  simp only [lookaheadDist, constrainPP]
  have hmul : gain * absRat speed1 ≤ gain * absRat speed2 :=
    Rat.mul_le_mul_of_nonneg_left hs hg
  by_cases h1a : gain * absRat speed1 < lMin
  · simp only [if_pos h1a]
    by_cases h2a : gain * absRat speed2 < lMin
    · simp only [if_pos h2a]; exact Rat.le_refl
    · simp only [if_neg h2a]
      by_cases h2b : gain * absRat speed2 > lMax
      · simp only [if_pos h2b]; exact h
      · simp only [if_neg h2b]; exact Rat.not_lt.mp h2a
  · simp only [if_neg h1a]
    by_cases h1b : gain * absRat speed1 > lMax
    · simp only [if_pos h1b]
      have h2a : ¬ (gain * absRat speed2 < lMin) := fun hlt =>
        absurd (Rat.le_trans (Rat.le_trans h (Rat.le_of_lt h1b)) hmul) (Rat.not_le.mpr hlt)
      have h2b : gain * absRat speed2 > lMax :=
        Rat.lt_of_le_of_ne
          (Rat.le_trans (Rat.le_of_lt h1b) hmul)
          (fun heq => absurd (heq.symm ▸ hmul) (Rat.not_le.mpr h1b))
      simp only [if_neg h2a, if_pos h2b]; exact Rat.le_refl
    · simp only [if_neg h1b]
      have h2a : ¬ (gain * absRat speed2 < lMin) := fun hlt =>
        absurd (Rat.le_trans (Rat.not_lt.mp h1a) hmul) (Rat.not_le.mpr hlt)
      simp only [if_neg h2a]
      by_cases h2b : gain * absRat speed2 > lMax
      · simp only [if_pos h2b]; exact Rat.not_lt.mp h1b
      · simp only [if_neg h2b]; exact hmul

/-- **Configuration hazard**: when `lMax < lMin` (inverted bounds) and
    `gain * |speed| ≥ lMin`, the result is `lMax` (the smaller value) — the
    lookahead drops below the intended minimum. This documents a latent bug:
    passing inverted `(lMin, lMax)` to `math::constrain` silently misuses the
    function and returns an out-of-range lookahead at high speed. -/
theorem lookahead_inverted_bounds_high_speed (gain speed lMin lMax : Rat)
    (hinv : lMax < lMin) (hspeed : lMin ≤ gain * absRat speed) :
    lookaheadDist gain speed lMin lMax = lMax := by
  simp only [lookaheadDist, constrainPP]
  simp only [if_neg (Rat.not_lt.mpr hspeed)]
  have hgt : gain * absRat speed > lMax :=
    Rat.lt_of_le_of_ne
      (Rat.le_trans (Rat.le_of_lt hinv) hspeed)
      (fun heq => absurd (heq.symm ▸ hspeed) (Rat.not_le.mpr hinv))
  simp only [if_pos hgt]

end PX4.PurePursuit
