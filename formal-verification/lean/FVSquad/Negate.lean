/-!
# PX4 `negate<int16_t>` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::negate<int16_t>` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`, lines 258–268

## Model

We model `int16_t` as `Fin 65536` using two's complement bit patterns:
- Values `0..32767` represent non-negative integers `0..32767`
- Values `32768..65535` represent negative integers `-32768..-1`

The C++ `return -value` branch corresponds to two's complement negation:
`(65536 - v.val) % 65536`.

```cpp
template<>
constexpr int16_t negate<int16_t>(int16_t value)
{
    if (value == INT16_MAX) { return INT16_MIN; }   // 32767 → -32768
    else if (value == INT16_MIN) { return INT16_MAX; }  // -32768 → 32767
    return -value;
}
```

## Key Finding

**BUG**: The `INT16_MAX → INT16_MIN` special case is incorrect.
`-INT16_MAX = -32767` is representable in `int16_t` without overflow, so this
special case is unnecessary and causes the function to be **non-involutive**:

```
negate(negate(-32767)) = negate(INT16_MAX) = INT16_MIN = -32768 ≠ -32767
```

Only `INT16_MIN` needs a special case (since `-INT16_MIN` would overflow).

## Approximations / Out of Scope

- Only the `int16_t` specialization is modelled.
- The generic `negate<T>` template (with `static_assert(sizeof(T) > 2)`) is not modelled.
- IEEE 754 float negation is not modelled.
-/

namespace PX4.Negate

/-- Model of `math::negate<int16_t>` over `Fin 65536`.

    The `int16_t` values `INT16_MAX = 32767` and `INT16_MIN = -32768 = 32768 (bit pattern)`
    are handled by special cases; all other values use two's complement negation. -/
def negate16 (v : Fin 65536) : Fin 65536 :=
  if v.val = 32767 then ⟨32768, by decide⟩       -- INT16_MAX → INT16_MIN
  else if v.val = 32768 then ⟨32767, by decide⟩   -- INT16_MIN → INT16_MAX
  else ⟨(65536 - v.val) % 65536, by omega⟩         -- standard two's complement negation

-- =========================================================
-- Section 1: Boundary value behaviour
-- =========================================================

/-- Negating INT16_MAX (32767) gives INT16_MIN (-32768, bit pattern 32768). -/
theorem negate16_MAX_MIN : negate16 ⟨32767, by decide⟩ = ⟨32768, by decide⟩ := by decide

/-- Negating INT16_MIN (-32768, bit pattern 32768) gives INT16_MAX (32767). -/
theorem negate16_MIN_MAX : negate16 ⟨32768, by decide⟩ = ⟨32767, by decide⟩ := by decide

/-- Negating zero gives zero. -/
theorem negate16_zero : negate16 ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide

/-- Negating +1 gives the bit pattern for -1 (65535). -/
theorem negate16_pos_one : negate16 ⟨1, by decide⟩ = ⟨65535, by decide⟩ := by decide

/-- Negating -1 (bit pattern 65535) gives +1. -/
theorem negate16_neg_one : negate16 ⟨65535, by decide⟩ = ⟨1, by decide⟩ := by decide

-- =========================================================
-- Section 2: The involution bug
-- =========================================================

/-- BUG FINDING: `negate16` is NOT a global involution.

    Counterexample: v = 32769, the bit pattern for -32767 in two's complement.
    - `negate16(32769)` = 32767 (= INT16_MAX), via the else branch:
      `(65536 − 32769) % 65536 = 32767`
    - `negate16(32767)` = 32768 (= INT16_MIN), via the INT16_MAX special case

    So `negate16(negate16(-32767)) = INT16_MIN = -32768 ≠ -32767`.

    This is a bug: `−INT16_MAX = −32767` is representable in `int16_t`, so the
    `INT16_MAX → INT16_MIN` special case is incorrect. Only `INT16_MIN` needs
    special treatment (since `−INT16_MIN = +32768` would overflow). -/
theorem negate16_not_involution :
    ¬ ∀ v : Fin 65536, negate16 (negate16 v) = v := by
  intro h
  exact absurd (h ⟨32769, by decide⟩) (by decide)

/-- The specific counterexample: `negate16(negate16(32769)) = 32768 ≠ 32769`. -/
theorem negate16_counterexample :
    negate16 (negate16 ⟨32769, by decide⟩) = ⟨32768, by decide⟩ := by decide

-- =========================================================
-- Section 3: Involution holds for safe subranges
-- =========================================================

/-- `negate16` IS an involution for positive values in [1, 32766].

    These are all non-zero, non-extreme positive int16 values. Their negations land in
    [32770, 65535], which avoid both special cases, so the second application is also
    via the standard branch and recovers the original value. -/
theorem negate16_pos_invol (v : Fin 65536) (hlo : 1 ≤ v.val) (hhi : v.val ≤ 32766) :
    negate16 (negate16 v) = v := by
  have hlt := v.isLt
  have hn1 : v.val ≠ 32767 := by omega
  have hn2 : v.val ≠ 32768 := by omega
  -- Concretize the inner result: negate16 v = ⟨65536 - v.val, _⟩
  have h_nv : negate16 v = ⟨65536 - v.val, by omega⟩ := by
    apply Fin.ext
    simp only [negate16, if_neg hn1, if_neg hn2]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_nv]
  -- 65536 - v.val ∈ [32770, 65535], avoiding both special cases
  have hn3 : 65536 - v.val ≠ 32767 := by omega
  have hn4 : 65536 - v.val ≠ 32768 := by omega
  apply Fin.ext
  simp only [negate16, if_neg hn3, if_neg hn4]
  -- goal: (65536 - (65536 - v.val)) % 65536 = v.val
  have h5 : 65536 - (65536 - v.val) = v.val := by omega
  simp only [h5]
  exact Nat.mod_eq_of_lt hlt

/-- `negate16` IS an involution for "high negative" values in [32770, 65535].

    These represent int16 values in [-32766, -2] (excluding INT16_MIN and -32767).
    Their negations land in [1, 32766], which avoid both special cases, so both
    applications use the standard branch and the round-trip holds. -/
theorem negate16_high_invol (v : Fin 65536) (hlo : 32770 ≤ v.val) :
    negate16 (negate16 v) = v := by
  have hlt := v.isLt
  have hn1 : v.val ≠ 32767 := by omega
  have hn2 : v.val ≠ 32768 := by omega
  -- Concretize the inner result: negate16 v = ⟨65536 - v.val, _⟩
  have h_nv : negate16 v = ⟨65536 - v.val, by omega⟩ := by
    apply Fin.ext
    simp only [negate16, if_neg hn1, if_neg hn2]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_nv]
  -- 65536 - v.val ∈ [1, 32766], avoiding both special cases
  have hn3 : 65536 - v.val ≠ 32767 := by omega
  have hn4 : 65536 - v.val ≠ 32768 := by omega
  apply Fin.ext
  simp only [negate16, if_neg hn3, if_neg hn4]
  -- goal: (65536 - (65536 - v.val)) % 65536 = v.val
  have h5 : 65536 - (65536 - v.val) = v.val := by omega
  simp only [h5]
  exact Nat.mod_eq_of_lt hlt

/-- `negate16` is an involution at INT16_MAX: negate16(negate16(INT16_MAX)) = INT16_MAX. -/
theorem negate16_MAX_invol : negate16 (negate16 ⟨32767, by decide⟩) = ⟨32767, by decide⟩ := by
  decide

/-- `negate16` is an involution at INT16_MIN: negate16(negate16(INT16_MIN)) = INT16_MIN. -/
theorem negate16_MIN_invol : negate16 (negate16 ⟨32768, by decide⟩) = ⟨32768, by decide⟩ := by
  decide

-- =========================================================
-- Section 4: Standard negation for non-special values
-- =========================================================

/-- For values other than INT16_MAX and INT16_MIN, `negate16` computes the
    standard two's complement negation `(65536 − v.val) % 65536`. -/
theorem negate16_standard (v : Fin 65536) (h1 : v.val ≠ 32767) (h2 : v.val ≠ 32768) :
    (negate16 v).val = (65536 - v.val) % 65536 := by
  simp [negate16, h1, h2]

/-- The result of `negate16` always has a valid Fin 65536 value (trivially true). -/
theorem negate16_in_range (v : Fin 65536) : (negate16 v).val < 65536 :=
  (negate16 v).isLt

/-! ## Summary of proved properties

  | Theorem                    | Statement                                                   | Status   |
  |----------------------------|-------------------------------------------------------------|----------|
  | `negate16_MAX_MIN`         | `negate16(INT16_MAX) = INT16_MIN`                           | ✅ Proved |
  | `negate16_MIN_MAX`         | `negate16(INT16_MIN) = INT16_MAX`                           | ✅ Proved |
  | `negate16_zero`            | `negate16(0) = 0`                                           | ✅ Proved |
  | `negate16_pos_one`         | `negate16(1) = 65535` (= −1)                                | ✅ Proved |
  | `negate16_neg_one`         | `negate16(65535) = 1`                                       | ✅ Proved |
  | `negate16_not_involution`  | `¬ ∀ v, negate16(negate16(v)) = v` — **BUG FOUND**         | ✅ Proved |
  | `negate16_counterexample`  | `negate16(negate16(32769)) = 32768 ≠ 32769`                 | ✅ Proved |
  | `negate16_pos_invol`       | Involution for `v.val ∈ [1, 32766]`                         | ✅ Proved |
  | `negate16_high_invol`      | Involution for `v.val ∈ [32770, 65535]`                     | ✅ Proved |
  | `negate16_MAX_invol`       | `negate16(negate16(INT16_MAX)) = INT16_MAX`                 | ✅ Proved |
  | `negate16_MIN_invol`       | `negate16(negate16(INT16_MIN)) = INT16_MIN`                 | ✅ Proved |
  | `negate16_standard`        | For non-special values: standard two's complement negation  | ✅ Proved |
  | `negate16_in_range`        | Result always in valid Fin 65536 range                      | ✅ Proved |

  **Bug**: `negate16(negate16(-32767)) = INT16_MIN ≠ -32767`. The INT16_MAX special
  case is incorrect and should be removed.
-/

end PX4.Negate
