#!/usr/bin/env python3
"""
Correspondence tests for `math::countSetBits` (PX4-Autopilot).

🔬 Lean Squad automated formal verification.

Compares the Lean 4 model `PX4.CountSetBits.countBits` (in
`formal-verification/lean/FVSquad/CountSetBits.lean`) against
Python's built-in `bin(n).count('1')` (which is an exact reference
implementation of the Hamming weight for non-negative integers).

The two models are semantically equivalent for `Nat`:
- Lean model: structural recursion on n / 2 and n % 2
- Python reference: count of '1' characters in binary string

Both implement the same popcount algorithm as the C++ while-loop:
  count += n & 1;  n >>= 1;

Run:
  python3 check_correspondence.py

Exit code 0 if all tests pass, 1 on any failure.
"""

import sys

def count_bits_lean_model(n: int) -> int:
    """
    Exact Python transcription of the Lean 4 `countBits` definition:
      countBits 0 = 0
      countBits (n+1) = (n+1) % 2 + countBits ((n+1) / 2)
    This matches the C++ while-loop behaviour for Nat inputs.
    """
    assert n >= 0
    result = 0
    while n:
        result += n % 2
        n = n // 2
    return result

def count_bits_reference(n: int) -> int:
    """Python built-in popcount reference."""
    assert n >= 0
    return bin(n).count('1')

def run_tests():
    failures = 0
    total = 0

    def check(n: int) -> None:
        nonlocal failures, total
        total += 1
        lean = count_bits_lean_model(n)
        ref  = count_bits_reference(n)
        if lean != ref:
            print(f"  FAIL  n={n}: lean={lean}, ref={ref}")
            failures += 1

    # --- Boundary and small values ---
    for n in range(0, 256):
        check(n)

    # --- Powers of 2: each should have exactly 1 set bit ---
    for k in range(0, 64):
        check(2 ** k)
        if count_bits_lean_model(2 ** k) != 1:
            print(f"  FAIL  countBits(2^{k}) = {count_bits_lean_model(2**k)}, expected 1")
            failures += 1

    # --- Powers of 2 minus 1: 2^k - 1 has k set bits ---
    for k in range(1, 33):
        n = (2 ** k) - 1
        check(n)
        expected = k
        got = count_bits_lean_model(n)
        if got != expected:
            print(f"  FAIL  countBits(2^{k}-1={n}) = {got}, expected {expected}")
            failures += 1

    # --- Specific values cited in the Lean file ---
    known = {
        0xFF:       8,
        0xAA:       4,
        0x55:       4,
        0xFFFF:     16,
        0xFFFFFFFF: 32,
        0:          0,
        1:          1,
        2:          1,
        3:          2,
        4:          1,
        7:          3,
        8:          1,
        15:         4,
        16:         1,
    }
    for n, expected in known.items():
        got = count_bits_lean_model(n)
        ref = count_bits_reference(n)
        total += 1
        ok = (got == expected == ref)
        if not ok:
            print(f"  FAIL  countBits({hex(n)}) = {got}, expected {expected}, ref={ref}")
            failures += 1

    # --- 64-bit values (large) ---
    large_values = [
        (0xFFFFFFFFFFFFFFFF, 64),
        (0xAAAAAAAAAAAAAAAA, 32),
        (0x5555555555555555, 32),
        (0x0F0F0F0F0F0F0F0F, 32),
        (1 << 63, 1),
    ]
    for n, expected in large_values:
        got = count_bits_lean_model(n)
        ref = count_bits_reference(n)
        total += 1
        if got != expected or got != ref:
            print(f"  FAIL  countBits(0x{n:016X}) = {got}, expected {expected}")
            failures += 1

    # --- Random-like spread: 500 values from a simple LCG sequence ---
    x = 0xDEADBEEF_12345678
    for _ in range(500):
        x = (x * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFFFFFFFFFF
        check(x)

    print(f"countSetBits correspondence: {total - failures}/{total} passed", end="")
    if failures:
        print(f"  ({failures} FAILED)")
        return 1
    else:
        print()
        return 0

if __name__ == "__main__":
    sys.exit(run_tests())
