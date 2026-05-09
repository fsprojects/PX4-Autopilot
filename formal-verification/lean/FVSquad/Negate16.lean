/-!
# PX4 `math::negate<int16_t>` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of the `int16_t` specialisation
of `math::negate` from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`, lines 257–270
- **Informal spec**: `formal-verification/specs/negate16_informal.md`

## C++ Source

```cpp
template<>
constexpr int16_t negate<int16_t>(int16_t value)
{
    if (value == INT16_MAX) {
        return INT16_MIN;
    } else if (value == INT16_MIN) {
        return INT16_MAX;
    }
    return -value;
}
```

## Model

We model `int16_t` values as `Int` in the range `[−32768, 32767]` and
define `negate16` matching the C++ logic exactly.

The boundary cases exist to avoid C++ undefined behaviour (negating `INT16_MIN`
would overflow) and to create a bijective map on the `int16_t` domain.

## Approximations / out of scope

- Only `int16_t` specialisation is modelled; the generic `negate<T>` template
  is not considered here.
- Bit-level representation (two's-complement layout) is not modelled; we reason
  at the arithmetic level.
- Inputs outside `[INT16_MIN, INT16_MAX]` are not in scope.

## Key Finding

`negate16` is **not** a self-inverse (involution) on its full domain.
For `x = −32767` (= `−INT16_MAX`), `negate16(negate16(−32767)) = −32768 ≠ −32767`.
This is the only exception in `[INT16_MIN, INT16_MAX]`.
See `negate16_not_involutive` and `negate16_involutive_iff`.
-/

namespace PX4.Negate16

-- ============================================================
-- § 0  Constants and definition
-- ============================================================

/-- Minimum value of `int16_t` in C++: `−2^15 = −32768`. -/
def INT16_MIN : Int := -32768

/-- Maximum value of `int16_t` in C++: `2^15 − 1 = 32767`. -/
def INT16_MAX : Int := 32767

/-- The `int16_t` specialisation of `math::negate`.

    Matches the C++ implementation exactly:
    - `INT16_MAX` maps to `INT16_MIN` (avoids the unintuitive asymmetry)
    - `INT16_MIN` maps to `INT16_MAX` (avoids C++ UB: `−INT16_MIN` overflows)
    - All other values map to their mathematical negation `-x`
-/
def negate16 (x : Int) : Int :=
  if x == INT16_MAX then INT16_MIN
  else if x == INT16_MIN then INT16_MAX
  else -x

-- Sanity checks
#eval negate16 32767   -- -32768  (INT16_MAX → INT16_MIN)
#eval negate16 (-32768) -- 32767  (INT16_MIN → INT16_MAX)
#eval negate16 0        -- 0
#eval negate16 1        -- -1
#eval negate16 (-1)     -- 1
#eval negate16 (-32767) -- 32767  (then: negate16 32767 = -32768 ≠ -32767 → not involutive)

-- ============================================================
-- § 1  Boundary values
-- ============================================================

/-- `negate16(INT16_MAX) = INT16_MIN`: the maximum maps to the minimum. -/
theorem negate16_MAX : negate16 INT16_MAX = INT16_MIN := by decide

/-- `negate16(INT16_MIN) = INT16_MAX`: the minimum maps to the maximum. -/
theorem negate16_MIN : negate16 INT16_MIN = INT16_MAX := by decide

/-- `negate16(0) = 0`: zero is a fixed point. -/
theorem negate16_zero : negate16 0 = 0 := by decide

-- ============================================================
-- § 2  Interior behaviour
-- ============================================================

/-- For `x` not at either boundary, `negate16` is exact mathematical negation. -/
theorem negate16_eq_neg (x : Int) (h1 : x ≠ INT16_MAX) (h2 : x ≠ INT16_MIN) :
    negate16 x = -x := by
  unfold negate16 INT16_MAX INT16_MIN at *
  simp only [beq_iff_eq]
  by_cases hx1 : x = 32767
  · exact absurd hx1 h1
  · by_cases hx2 : x = -32768
    · exact absurd hx2 h2
    · simp [hx1, hx2]

/-- `negate16(1) = -1`. -/
theorem negate16_one : negate16 1 = -1 := by decide

/-- `negate16(-1) = 1`. -/
theorem negate16_neg_one : negate16 (-1) = 1 := by decide

-- ============================================================
-- § 3  Range: result stays in [INT16_MIN, INT16_MAX]
-- ============================================================

/-- When `x ∈ [INT16_MIN, INT16_MAX]`, the result is also in `[INT16_MIN, INT16_MAX]`.

    This is a key safety property: `negate16` cannot produce an out-of-range value. -/
theorem negate16_in_range (x : Int) (h_lo : INT16_MIN ≤ x) (h_hi : x ≤ INT16_MAX) :
    INT16_MIN ≤ negate16 x ∧ negate16 x ≤ INT16_MAX := by
  unfold negate16 INT16_MIN INT16_MAX at *
  simp only [beq_iff_eq]
  by_cases h1 : x = 32767
  · simp only [h1, ↓reduceIte]; omega
  · by_cases h2 : x = -32768
    · simp only [h1, h2, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

-- ============================================================
-- § 4  Non-injectivity: a structural property
-- ============================================================

/-- **FINDING**: `negate16` is **not** injective.

    Both `−32767 = −INT16_MAX` and `INT16_MIN = −32768` map to `32767 = INT16_MAX`.
    This is a consequence of the boundary mapping `INT16_MAX → INT16_MIN`. -/
theorem negate16_not_injective :
    negate16 (-32767) = negate16 (-32768) ∧ (-32767 : Int) ≠ -32768 := by decide

/-- The two inputs that collide under `negate16`. -/
theorem negate16_collision : negate16 (-32767) = 32767 ∧ negate16 (-32768) = 32767 := by decide

/-- `−32767` is not in the image of `negate16` on `[INT16_MIN, INT16_MAX]`.

    No value in `[INT16_MIN, INT16_MAX]` maps to `−32767` under `negate16`. -/
theorem negate16_no_preimage_neg32767 (x : Int)
    (h_lo : INT16_MIN ≤ x) (h_hi : x ≤ INT16_MAX) :
    negate16 x ≠ -32767 := by
  unfold negate16 INT16_MIN INT16_MAX at *
  simp only [beq_iff_eq]
  by_cases h1 : x = 32767
  · simp only [h1, ↓reduceIte]; omega
  · by_cases h2 : x = -32768
    · simp only [h1, h2, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

-- ============================================================
-- § 5  Involutivity (self-inverse) — and its exception
-- ============================================================

/-- **FINDING**: `negate16` is **not** a self-inverse for `x = −32767`.

    `negate16(−32767) = INT16_MAX = 32767`,
    then `negate16(32767) = INT16_MIN = −32768 ≠ −32767`.

    This is the only point in `[INT16_MIN, INT16_MAX]` where `negate16 ∘ negate16 ≠ id`.
    The root cause: `INT16_MAX` maps to `INT16_MIN` (not to `−INT16_MAX = −32767`),
    so applying `negate16` twice to `−32767` lands at `INT16_MIN`, not back at `−32767`.
-/
theorem negate16_not_involutive :
    negate16 (negate16 (-32767)) ≠ -32767 := by decide

/-- **Iff characterisation**: `negate16(negate16(x)) = x` if and only if `x ≠ −INT16_MAX`.

    In range `[INT16_MIN, INT16_MAX]`, `negate16` is self-inverse **everywhere except**
    `x = −32767 = −INT16_MAX`. -/
theorem negate16_involutive_iff (x : Int)
    (h_lo : INT16_MIN ≤ x) (h_hi : x ≤ INT16_MAX) :
    negate16 (negate16 x) = x ↔ x ≠ -INT16_MAX := by
  unfold negate16 INT16_MIN INT16_MAX at *
  simp only [beq_iff_eq]
  constructor
  · intro h hc
    -- x = -32767; negate16(-32767) = 32767; negate16(32767) = -32768 ≠ -32767
    by_cases hx1 : x = 32767
    · simp only [hx1, ↓reduceIte] at h; omega
    · by_cases hx2 : x = -32768
      · simp only [hx1, hx2, ↓reduceIte] at h; omega
      · simp only [hx1, hx2, ↓reduceIte] at h
        by_cases hn1 : -x = 32767
        · simp only [hn1, ↓reduceIte] at h; omega
        · by_cases hn2 : -x = -32768
          · simp only [hn1, hn2, ↓reduceIte] at h; omega
          · simp only [hn1, hn2, ↓reduceIte] at h; omega
  · intro h
    by_cases hx1 : x = 32767
    · simp only [hx1, ↓reduceIte]; decide
    · by_cases hx2 : x = -32768
      · simp only [hx1, hx2, ↓reduceIte]; decide
      · simp only [hx1, hx2, ↓reduceIte]
        by_cases hn1 : -x = 32767
        · -- h says x ≠ -32767, but -x = 32767 means x = -32767
          exfalso; apply h; omega
        · by_cases hn2 : -x = -32768
          · simp only [hn1, hn2, ↓reduceIte]; omega
          · simp only [hn1, hn2, ↓reduceIte]; omega

/-- `negate16` is involutive for `x = INT16_MAX`. -/
theorem negate16_involutive_MAX : negate16 (negate16 INT16_MAX) = INT16_MAX := by decide

/-- `negate16` is involutive for `x = INT16_MIN`. -/
theorem negate16_involutive_MIN : negate16 (negate16 INT16_MIN) = INT16_MIN := by decide

/-- `negate16` is involutive for all interior points except `−INT16_MAX`. -/
theorem negate16_involutive_interior (x : Int)
    (h_lo : INT16_MIN ≤ x) (h_hi : x ≤ INT16_MAX)
    (h_excl : x ≠ -INT16_MAX) :
    negate16 (negate16 x) = x :=
  (negate16_involutive_iff x h_lo h_hi).mpr h_excl

-- ============================================================
-- § 6  Concrete values
-- ============================================================

/-- `negate16(−32767) = 32767`: the only anomalous interior point. -/
theorem negate16_neg32767 : negate16 (-32767) = 32767 := by decide

/-- `negate16(100) = −100`: typical interior value. -/
theorem negate16_100 : negate16 100 = -100 := by decide

/-- `negate16(−100) = 100`: typical interior value. -/
theorem negate16_neg100 : negate16 (-100) = 100 := by decide

end PX4.Negate16
