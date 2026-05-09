# `countSetBits` Correspondence Tests

🔬 *Lean Squad automated formal verification.*

This directory contains Route B correspondence tests for `math::countSetBits`,
verifying that the Lean 4 model in
`formal-verification/lean/FVSquad/CountSetBits.lean` agrees with
Python's reference popcount on a large and representative set of inputs.

## What Is Tested

| C++ implementation | Lean 4 model |
|---|---|
| `math::countSetBits<T>(n)` while-loop | `PX4.CountSetBits.countBits n` recursive def |

### C++ algorithm (from `src/lib/mathlib/math/Functions.hpp`)

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

### Lean 4 model

```lean
def countBits : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let m := n + 1
    m % 2 + countBits (m / 2)
```

Both compute the **Hamming weight** (popcount): the number of 1-bits in the
binary representation of `n`.

## Correspondence Level

**Exact** for all natural-number inputs: the Lean recursive definition and the
C++ while-loop compute the same value for every non-negative integer.

- C++ right-shift `n >>= 1` corresponds to integer division `n / 2`.
- C++ bitmask `n & 1` corresponds to modulo `n % 2`.

## How to Run

```bash
python3 formal-verification/tests/count_set_bits/check_correspondence.py
```

Expected output:
```
countSetBits correspondence: 871/871 passed
```

Exit code 0 on success, 1 on any failure.

## Test Coverage

| Category | Cases |
|----------|-------|
| All values 0–255 | 256 |
| Powers of 2 (2^0 – 2^63): popcount = 1 | 64 |
| Powers-of-2 minus 1 (2^k – 1): popcount = k | 32 |
| Known values from Lean theorems | 15 |
| 64-bit boundary values | 5 |
| LCG pseudo-random 64-bit values | 500 |
| **Total** | **871** |

## What Is NOT Tested

- **Signed integer overloads**: the C++ template supports signed types, but
  for negative values the C++ behaviour is implementation-defined. The Lean
  model covers only `Nat` (unsigned).
- **Overflow of `int count`**: theoretically impossible for 64-bit inputs
  (count ≤ 64), not tested explicitly.
- **SIMD/hardware popcount**: the compiler may replace the loop with `POPCNT`.
  This is semantically transparent but not tested here.
