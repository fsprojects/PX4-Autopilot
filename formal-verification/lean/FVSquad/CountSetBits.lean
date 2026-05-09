/-!
# PX4 `countSetBits` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::countSetBits` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp` (approx. line 266)
- **Used in**: bitmask occupancy checks in sensor fusion, protocol validation, and
  collision-avoidance bitmask processing throughout PX4.

## C++ Reference

```cpp
template<typename T>
int countSetBits(T n)
{
    int count = 0;
    while (n) {
        count += n & 1;
        n >>= 1;
    }
    return count;
}
```

`countSetBits` computes the **Hamming weight** (popcount): the number of `1`-bits
in the binary representation of a non-negative integer.

## Model

We model the function over `Nat` (natural numbers), capturing the semantics of
the C++ unsigned integer overloads.

```
countBits 0     = 0
countBits (n+1) = (n+1) % 2 + countBits ((n+1) / 2)
```

The definition unfolds the loop as structural recursion on the bit-shifted value.

## Approximations / Out of Scope

- **Signed integer overloads**: the C++ template can be called with signed types;
  we model only the `Nat` (unsigned) case.  For negative signed integers the C++
  behaviour is implementation-defined.
- **Fixed-width overflow**: `int count` cannot overflow for 64-bit inputs (count ≤ 64).
  The `Nat` model avoids overflow entirely.
- **SIMD / hardware popcount**: the compiler may replace this loop with a single
  `POPCNT` instruction.  The Lean model proves the algorithm is correct; the
  hardware-optimisation correspondence is out of scope.

## Theorems Summary

| Theorem | Description | Proof |
|---------|-------------|-------|
| `countBits_zero` | `countBits 0 = 0` | ✅ `simp` |
| `countBits_recurse` | `n > 0 → countBits n = n % 2 + countBits (n / 2)` | ✅ `simp` |
| `countBits_even` | `countBits (2 * k) = countBits k` | ✅ proved |
| `countBits_odd` | `countBits (2 * k + 1) = countBits k + 1` | ✅ proved |
| `countBits_pos` | `n > 0 → countBits n > 0` | ✅ structural recursion |
| `countBits_le` | `countBits n ≤ n` | ✅ structural recursion |
| `countBits_zero_iff` | `countBits n = 0 ↔ n = 0` | ✅ proved |
| `countBits_pow2` | `countBits (2 ^ k) = 1` | ✅ induction |
| `countBits_eq_one_imp_pow2` | `countBits n = 1 → ∃ k, n = 2 ^ k` | ✅ structural recursion |
| `countBits_eq_one_iff_pow2` | `countBits n = 1 ↔ ∃ k, n = 2 ^ k` | ✅ proved |
| Concrete values | `countBits 0xFF = 8`, etc. | ✅ `native_decide` |
-/

namespace PX4.CountSetBits

/-! ## Definition -/

/-- Lean model of `math::countSetBits<T>` for unsigned/natural inputs.
Returns the number of 1-bits in the binary representation of `n` (Hamming weight). -/
def countBits : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let m := n + 1
    m % 2 + countBits (m / 2)
termination_by n => n

/-! ## Basic computation -/

theorem countBits_zero : countBits 0 = 0 := by simp [countBits]

theorem countBits_one : countBits 1 = 1 := by native_decide

theorem countBits_two : countBits 2 = 1 := by native_decide

theorem countBits_three : countBits 3 = 2 := by native_decide

/-- The standard popcount recurrence: for `n > 0`,
    `countBits n = n % 2 + countBits (n / 2)`.
    Corresponds to `count += n & 1; n >>= 1` in the C++ loop. -/
theorem countBits_recurse (n : Nat) (h : 0 < n) :
    countBits n = n % 2 + countBits (n / 2) := by
  cases n with
  | zero => omega
  | succ k => simp [countBits]

/-! ## Structural lemmas: even and odd inputs -/

/-- Left-shifting (multiplying by 2) does not change the bit count.
    Corresponds to: `n` and `2 * n` have the same popcount
    since the added zero bit contributes nothing. -/
theorem countBits_even (k : Nat) : countBits (2 * k) = countBits k := by
  cases k with
  | zero => simp [countBits]
  | succ m =>
    rw [countBits_recurse _ (by omega)]
    have hmod : (2 * (m + 1)) % 2 = 0 := by omega
    have hdiv : (2 * (m + 1)) / 2 = m + 1 := by omega
    simp [hmod, hdiv]

/-- Adding a set LSB (making the number odd) increments the bit count by one. -/
theorem countBits_odd (k : Nat) : countBits (2 * k + 1) = countBits k + 1 := by
  rw [countBits_recurse _ (by omega)]
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [hmod, hdiv]; omega

/-! ## Core correctness theorems -/

-- Private recursive lemma for countBits_pos
private def countBitsPos_aux : (n : Nat) → 0 < n → 0 < countBits n
  | 0, h => absurd h (by omega)
  | n + 1, _ => by
    rw [countBits_recurse _ (by omega)]
    by_cases hmod : (n + 1) % 2 = 1
    · omega
    · have : (n + 1) % 2 = 0 := by omega
      simp [this]
      exact countBitsPos_aux _ (by omega)
termination_by n => n

/-- Any positive integer has at least one set bit. -/
theorem countBits_pos (n : Nat) (h : 0 < n) : 0 < countBits n :=
  countBitsPos_aux n h

-- Private recursive lemma for countBits_le
private def countBitsLe_aux : (n : Nat) → countBits n ≤ n
  | 0 => by simp [countBits]
  | n + 1 => by
    rw [countBits_recurse _ (by omega)]
    have h2 := countBitsLe_aux ((n + 1) / 2)
    have h3 : (n + 1) / 2 ≤ n := by omega
    omega
termination_by n => n

/-- The Hamming weight never exceeds the number itself. -/
theorem countBits_le (n : Nat) : countBits n ≤ n :=
  countBitsLe_aux n

/-- The Hamming weight is zero if and only if the number is zero. -/
theorem countBits_zero_iff (n : Nat) : countBits n = 0 ↔ n = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact hn
    · have := countBits_pos n hn; omega
  · intro hne
    subst hne
    exact countBits_zero

/-- Powers of two have exactly one set bit. -/
theorem countBits_pow2 (k : Nat) : countBits (2 ^ k) = 1 := by
  induction k with
  | zero => native_decide
  | succ n ih =>
    have heq : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [heq, countBits_even]
    exact ih

-- Private recursive helper for countBits_eq_one_imp_pow2
private def countBitsOnePow2_aux : (n : Nat) → countBits n = 1 → ∃ k : Nat, n = 2 ^ k
  | 0, h => by simp [countBits] at h
  | n + 1, h => by
    rw [countBits_recurse _ (by omega)] at h
    by_cases hmod : (n + 1) % 2 = 1
    · simp [hmod] at h
      have hdiv : (n + 1) / 2 = 0 := by rwa [countBits_zero_iff] at h
      exact ⟨0, by omega⟩
    · have hmod0 : (n + 1) % 2 = 0 := by omega
      simp [hmod0] at h
      obtain ⟨k, hk⟩ := countBitsOnePow2_aux _ h
      exact ⟨k + 1, by rw [Nat.pow_succ]; omega⟩
termination_by n => n

/-- If a number has exactly one set bit, it is a power of two. -/
theorem countBits_eq_one_imp_pow2 (n : Nat) (h : countBits n = 1) :
    ∃ k : Nat, n = 2 ^ k :=
  countBitsOnePow2_aux n h

/-- Full characterisation: `countBits n = 1` iff `n` is a power of two. -/
theorem countBits_eq_one_iff_pow2 (n : Nat) :
    countBits n = 1 ↔ ∃ k : Nat, n = 2 ^ k := by
  constructor
  · exact countBits_eq_one_imp_pow2 n
  · rintro ⟨k, rfl⟩
    exact countBits_pow2 k

/-! ## Concrete values (by native_decide) -/

theorem countBits_4   : countBits 4 = 1 := by native_decide
theorem countBits_7   : countBits 7 = 3 := by native_decide
theorem countBits_8   : countBits 8 = 1 := by native_decide
theorem countBits_15  : countBits 15 = 4 := by native_decide
theorem countBits_16  : countBits 16 = 1 := by native_decide

/-- All 8 bits set in a full byte. -/
theorem countBits_0xFF : countBits 0xFF = 8 := by native_decide

/-- Alternating bits (`0xAA = 10101010₂`): 4 set bits. -/
theorem countBits_0xAA : countBits 0xAA = 4 := by native_decide

/-- Alternating bits (`0x55 = 01010101₂`): 4 set bits. -/
theorem countBits_0x55 : countBits 0x55 = 4 := by native_decide

/-- Full 16-bit mask. -/
theorem countBits_0xFFFF : countBits 0xFFFF = 16 := by native_decide

/-- Full 32-bit mask. -/
theorem countBits_0xFFFFFFFF : countBits 0xFFFFFFFF = 32 := by native_decide

/-- `0xAA` and `0x55` are bitwise complements with the same popcount: 4. -/
theorem countBits_AA_eq_55 : countBits 0xAA = countBits 0x55 := by native_decide

end PX4.CountSetBits
