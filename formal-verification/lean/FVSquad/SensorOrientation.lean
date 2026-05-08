/-!
# PX4 SensorOrientation — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `sensor_orientation_to_yaw_offset`
from PX4-Autopilot's collision-prevention library, for the non-CUSTOM cases.

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp`
- **C++ header**: `src/lib/collision_prevention/ObstacleMath.hpp`

## C++ reference

```cpp
enum SensorOrientation {
  ROTATION_YAW_0   = 0,
  ROTATION_YAW_45  = 1,
  ROTATION_YAW_90  = 2,
  ROTATION_YAW_135 = 3,
  ROTATION_YAW_180 = 4,
  ROTATION_YAW_225 = 5,
  ROTATION_YAW_270 = 6,
  ROTATION_YAW_315 = 7,
  ROTATION_CUSTOM  = 100,
  ...
};

float sensor_orientation_to_yaw_offset(const SensorOrientation orientation, const float q[4]) {
  float offset = 0.0f;
  switch (orientation) {
    case ROTATION_YAW_0:   offset = 0.0f;              break;
    case ROTATION_YAW_45:  offset = M_PI_F / 4.0f;     break;
    case ROTATION_YAW_90:  offset = M_PI_F / 2.0f;     break;
    case ROTATION_YAW_135: offset = 3.0f * M_PI_F / 4.0f; break;
    case ROTATION_YAW_180: offset = M_PI_F;             break;
    case ROTATION_YAW_225: offset = -3.0f * M_PI_F / 4.0f; break;
    case ROTATION_YAW_270: offset = -M_PI_F / 2.0f;    break;
    case ROTATION_YAW_315: offset = -M_PI_F / 4.0f;    break;
    case ROTATION_CUSTOM:  offset = /* quaternion */ ...; break;
  }
  return offset;
}
```

## Model

Since `π` is irrational, we model the output as an **integer multiplier `k`** such that
the true offset is `k * (π/4)`.  This lets us reason about the function using only exact
integer arithmetic while capturing all the essential properties:

- YAW_0   → k = 0   (offset = 0)
- YAW_45  → k = 1   (offset = π/4)
- YAW_90  → k = 2   (offset = π/2)
- YAW_135 → k = 3   (offset = 3π/4)
- YAW_180 → k = 4   (offset = π)
- YAW_225 → k = -3  (offset = -3π/4)
- YAW_270 → k = -2  (offset = -π/2)
- YAW_315 → k = -1  (offset = -π/4)

The CUSTOM case depends on quaternion math and is **excluded** from this model.

## Key properties proved

1. **Range containment**: `-3 ≤ k ≤ 4` for all non-CUSTOM orientations
   (equivalently, `|offset| ≤ π`)
2. **Injectivity**: distinct orientations → distinct k values
3. **Symmetry**: k values are exactly the set `{-3, -2, -1, 0, 1, 2, 3, 4}`
4. **Exhaustiveness**: all 8 non-CUSTOM variants are covered

## Approximations / out of scope

- **IEEE 754 float semantics**: the exact float representation of `M_PI_F / 4.0f` etc.
  is not modelled; we model only the intended mathematical value.
- **ROTATION_CUSTOM case**: excluded because it requires quaternion arithmetic.
- **Integer aliases** (`ROTATION_FORWARD_FACING = 0`, etc.) are not modelled as
  separate constructors; they are aliases for YAW_0, YAW_90, YAW_180, YAW_270.
-/

namespace PX4.SensorOrientation

/-! ## Lean enum -/

/-- The 8 non-CUSTOM sensor orientation values.

    Note: `ROTATION_FORWARD_FACING = ROTATION_YAW_0`,
    `ROTATION_RIGHT_FACING = ROTATION_YAW_90`, etc. are aliases; they map to the
    same Lean constructor. -/
inductive Orientation : Type
  | yaw0
  | yaw45
  | yaw90
  | yaw135
  | yaw180
  | yaw225
  | yaw270
  | yaw315
deriving DecidableEq, Repr

/-- All 8 non-CUSTOM orientations as an explicit list. -/
def allOrientations : List Orientation :=
  [.yaw0, .yaw45, .yaw90, .yaw135, .yaw180, .yaw225, .yaw270, .yaw315]

/-! ## Lookup function -/

/-- Map each orientation to its integer quarter-turn multiplier `k`, where the
    true yaw offset is `k * (π/4)`.

    This models the non-CUSTOM cases of `sensor_orientation_to_yaw_offset`. -/
def toQuarterTurns : Orientation → Int
  | .yaw0   =>  0
  | .yaw45  =>  1
  | .yaw90  =>  2
  | .yaw135 =>  3
  | .yaw180 =>  4
  | .yaw225 => -3
  | .yaw270 => -2
  | .yaw315 => -1

/-! ## Concrete examples -/

#eval allOrientations.map toQuarterTurns
-- Expected: [0, 1, 2, 3, 4, -3, -2, -1]

/-! ## Range containment -/

/-- **Range containment**: for every non-CUSTOM orientation, `-3 ≤ k ≤ 4`.

    Equivalently: `|offset| ≤ π` (since `4 * (π/4) = π` and `|-3| * (π/4) = 3π/4 < π`).

    Proof: exhaustive case analysis by `decide`. -/
theorem toQuarterTurns_range (o : Orientation) :
    -3 ≤ toQuarterTurns o ∧ toQuarterTurns o ≤ 4 := by
  cases o <;> decide

/-- Lower bound: `toQuarterTurns o ≥ -3` for all non-CUSTOM orientations. -/
theorem toQuarterTurns_ge_neg3 (o : Orientation) : -3 ≤ toQuarterTurns o :=
  (toQuarterTurns_range o).1

/-- Upper bound: `toQuarterTurns o ≤ 4` for all non-CUSTOM orientations. -/
theorem toQuarterTurns_le_4 (o : Orientation) : toQuarterTurns o ≤ 4 :=
  (toQuarterTurns_range o).2

/-- **Absolute bound**: `|k| ≤ 4`, i.e. `|offset| ≤ π`. -/
theorem toQuarterTurns_abs_le_4 (o : Orientation) :
    Int.natAbs (toQuarterTurns o) ≤ 4 := by
  cases o <;> decide

/-! ## Injectivity -/

/-- **Injectivity**: distinct orientations yield distinct quarter-turn values.

    Proof: decidable equality via `decide`. -/
theorem toQuarterTurns_injective (o1 o2 : Orientation)
    (h : toQuarterTurns o1 = toQuarterTurns o2) : o1 = o2 := by
  cases o1 <;> cases o2 <;> simp_all [toQuarterTurns] <;> decide

/-- **Injectivity (iff form)**: `toQuarterTurns o1 = toQuarterTurns o2 ↔ o1 = o2`. -/
theorem toQuarterTurns_inj_iff (o1 o2 : Orientation) :
    toQuarterTurns o1 = toQuarterTurns o2 ↔ o1 = o2 :=
  ⟨toQuarterTurns_injective o1 o2, fun h => h ▸ rfl⟩

/-! ## Surjectivity onto the image set -/

/-- The image of `toQuarterTurns` is exactly `{-3, -2, -1, 0, 1, 2, 3, 4}`. -/
def imageSet : List Int := [-3, -2, -1, 0, 1, 2, 3, 4]

/-- Every k in imageSet is achieved by some orientation. -/
theorem toQuarterTurns_surjective_on_image :
    ∀ k ∈ imageSet, ∃ o : Orientation, toQuarterTurns o = k := by
  intro k hk
  simp [imageSet] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.yaw225, rfl⟩
  · exact ⟨.yaw270, rfl⟩
  · exact ⟨.yaw315, rfl⟩
  · exact ⟨.yaw0, rfl⟩
  · exact ⟨.yaw45, rfl⟩
  · exact ⟨.yaw90, rfl⟩
  · exact ⟨.yaw135, rfl⟩
  · exact ⟨.yaw180, rfl⟩

/-- Every value of `toQuarterTurns` is in the imageSet. -/
theorem toQuarterTurns_mem_imageSet (o : Orientation) :
    toQuarterTurns o ∈ imageSet := by
  cases o <;> decide

/-- The image has exactly 8 distinct values (one per orientation). -/
theorem imageSet_card : imageSet.length = 8 := by decide

/-- The values in imageSet are all distinct. -/
theorem imageSet_nodup : imageSet.Nodup := by decide

/-! ## Coverage of standard compass headings -/

/-- The 4 cardinal directions (N/E/S/W) are covered:
    0° → k=0, 90° → k=2, 180° → k=4, 270° → k=-2. -/
theorem cardinal_directions_covered :
    toQuarterTurns .yaw0   = 0 ∧
    toQuarterTurns .yaw90  = 2 ∧
    toQuarterTurns .yaw180 = 4 ∧
    toQuarterTurns .yaw270 = -2 := by decide

/-- The 4 intercardinal directions (NE/SE/SW/NW) are covered:
    45° → k=1, 135° → k=3, 225° → k=-3, 315° → k=-1. -/
theorem intercardinal_directions_covered :
    toQuarterTurns .yaw45  = 1 ∧
    toQuarterTurns .yaw135 = 3 ∧
    toQuarterTurns .yaw225 = -3 ∧
    toQuarterTurns .yaw315 = -1 := by decide

/-! ## Forward-facing alias correctness -/

/-- `ROTATION_FORWARD_FACING = ROTATION_YAW_0`: forward-facing maps to k=0. -/
theorem forward_facing_is_zero : toQuarterTurns .yaw0 = 0 := by decide

/-- `ROTATION_RIGHT_FACING = ROTATION_YAW_90`: right-facing maps to k=2. -/
theorem right_facing_is_yaw90 : toQuarterTurns .yaw90 = 2 := by decide

/-- `ROTATION_BACKWARD_FACING = ROTATION_YAW_180`: backward-facing maps to k=4. -/
theorem backward_facing_is_yaw180 : toQuarterTurns .yaw180 = 4 := by decide

/-- `ROTATION_LEFT_FACING = ROTATION_YAW_270`: left-facing maps to k=-2. -/
theorem left_facing_is_yaw270 : toQuarterTurns .yaw270 = -2 := by decide

/-! ## Odd-symmetry: yaw_x and yaw_(360-x) are negatives (mod 8 multiples of π/4) -/

/-- YAW_45 and YAW_315 are opposite: k₄₅ + k₃₁₅ = 0.
    Geometrically: +45° and -45° are symmetric about 0°. -/
theorem yaw45_yaw315_opposite :
    toQuarterTurns .yaw45 + toQuarterTurns .yaw315 = 0 := by decide

/-- YAW_90 and YAW_270 are opposite: k₉₀ + k₂₇₀ = 0. -/
theorem yaw90_yaw270_opposite :
    toQuarterTurns .yaw90 + toQuarterTurns .yaw270 = 0 := by decide

/-- YAW_135 and YAW_225 are opposite: k₁₃₅ + k₂₂₅ = 0. -/
theorem yaw135_yaw225_opposite :
    toQuarterTurns .yaw135 + toQuarterTurns .yaw225 = 0 := by decide

/-- YAW_180 is self-opposite with sign (k₁₈₀ = 4; complement is -4 = k₁₈₀ - 8). -/
theorem yaw180_value : toQuarterTurns .yaw180 = 4 := by decide

/-! ## Summary of proved properties

  | Theorem                               | Statement                                             | Status    |
  |---------------------------------------|-------------------------------------------------------|-----------|
  | `toQuarterTurns_range`                | `-3 ≤ k ≤ 4` for all orientations                    | ✅ Proved |
  | `toQuarterTurns_ge_neg3`              | `k ≥ -3` (lower bound)                                | ✅ Proved |
  | `toQuarterTurns_le_4`                 | `k ≤ 4` (upper bound)                                 | ✅ Proved |
  | `toQuarterTurns_abs_le_4`             | `|k| ≤ 4` (absolute bound, `|offset| ≤ π`)            | ✅ Proved |
  | `toQuarterTurns_injective`            | distinct orientations → distinct k                    | ✅ Proved |
  | `toQuarterTurns_inj_iff`              | `k₁ = k₂ ↔ o₁ = o₂`                                  | ✅ Proved |
  | `toQuarterTurns_surjective_on_image`  | every k in {-3,..,4} is achieved                      | ✅ Proved |
  | `toQuarterTurns_mem_imageSet`         | every output is in {-3,-2,-1,0,1,2,3,4}               | ✅ Proved |
  | `imageSet_card`                       | exactly 8 distinct image values                        | ✅ Proved |
  | `imageSet_nodup`                      | image values are all distinct                          | ✅ Proved |
  | `cardinal_directions_covered`         | N/E/S/W compass headings map correctly                 | ✅ Proved |
  | `intercardinal_directions_covered`    | NE/SE/SW/NW compass headings map correctly             | ✅ Proved |
  | `forward_facing_is_zero`              | FORWARD_FACING alias → k = 0                          | ✅ Proved |
  | `right_facing_is_yaw90`               | RIGHT_FACING alias → k = 2                            | ✅ Proved |
  | `backward_facing_is_yaw180`           | BACKWARD_FACING alias → k = 4                         | ✅ Proved |
  | `left_facing_is_yaw270`               | LEFT_FACING alias → k = -2                            | ✅ Proved |
  | `yaw45_yaw315_opposite`               | k₄₅ + k₃₁₅ = 0                                       | ✅ Proved |
  | `yaw90_yaw270_opposite`               | k₉₀ + k₂₇₀ = 0                                       | ✅ Proved |
  | `yaw135_yaw225_opposite`              | k₁₃₅ + k₂₂₅ = 0                                      | ✅ Proved |
  | `yaw180_value`                        | k₁₈₀ = 4                                             | ✅ Proved |
-/

end PX4.SensorOrientation
