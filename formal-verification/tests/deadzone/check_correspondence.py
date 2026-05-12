#!/usr/bin/env python3
"""
Route B Correspondence Tests: PX4 deadzone
🔬 Lean Squad automated formal verification.

Validates that the Lean 4 rational model of the deadzone function in
formal-verification/lean/FVSquad/Deadzone.lean produces results behaviourally
identical to the C++ template implementation in
src/lib/mathlib/math/Functions.hpp on a comprehensive set of rational inputs.

## Model summary

C++ source (src/lib/mathlib/math/Functions.hpp):
    template<typename T>
    const T deadzone(const T &value, const T &dz)
    {
        T x = constrain(value, (T)-1, (T)1);
        T dzc = constrain(dz, (T)0, (T)0.99);
        T out = (x - sign(x) * dzc) / (1 - dzc);
        return out * (fabsf(x) > dzc);
    }

Lean 4 model (Deadzone.lean, namespace PX4):
    def signR (x : Rat) : Rat :=
      if x ≥ 0 then 1 else -1

    def deadzone (x dz : Rat) : Rat :=
      if dz < 0 then x
      else if x > dz then (x - dz) / (1 - dz)
      else if x < -dz then (x + dz) / (1 - dz)
      else 0

The C++ implementation constrains `value` to [-1,1] and `dz` to [0,0.99];
for this correspondence test we use inputs already in those ranges so that
the constrain calls are identity, enabling direct comparison.

For inputs in domain [-1,1] × [0,0.99], the C++ formula:
    out = (x - sign(x)*dzc) / (1 - dzc)  if |x| > dzc, else 0
matches the Lean model:
    if x > dz then (x - dz) / (1 - dz)
    elif x < -dz then (x + dz) / (1 - dz)
    else 0
(since for x ≥ 0: sign(x)=1, so out=(x-dz)/(1-dz); for x<0: sign(x)=-1, so out=(x+dz)/(1-dz))

Usage:
    python3 check_correspondence.py

Exit code 0 on success, non-zero on any mismatch.
"""

import sys
from fractions import Fraction


# ── Lean model (exact translation from Deadzone.lean) ────────────────────────

def deadzone_lean(x: Fraction, dz: Fraction) -> Fraction:
    """Lean 4 model of PX4's deadzone function (Deadzone.lean).

    Assumes dz ≥ 0 and dz < 1 (the theorem preconditions).
    The Lean model has the special case 'if dz < 0 then x' which we
    handle, but all test inputs have dz ≥ 0.
    """
    if dz < Fraction(0):
        return x  # degenerate branch (not used in tests)
    if x > dz:
        return (x - dz) / (1 - dz)
    if x < -dz:
        return (x + dz) / (1 - dz)
    return Fraction(0)


# ── C++ reference (exact rational translation) ────────────────────────────────

def sign_rat(x: Fraction) -> Fraction:
    """C++ sign(x): returns +1 for x ≥ 0, -1 for x < 0."""
    return Fraction(1) if x >= Fraction(0) else Fraction(-1)


def constrain_rat(v: Fraction, lo: Fraction, hi: Fraction) -> Fraction:
    """constrain(v, lo, hi) — clamp v to [lo, hi]."""
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v


def deadzone_cpp(value: Fraction, dz: Fraction) -> Fraction:
    """C++ deadzone template, translated to exact rational arithmetic.

    Note: the C++ uses 0.99 as the upper clamp for dz. We represent 0.99
    exactly as Fraction(99, 100).
    """
    x = constrain_rat(value, Fraction(-1), Fraction(1))
    dzc = constrain_rat(dz, Fraction(0), Fraction(99, 100))
    out = (x - sign_rat(x) * dzc) / (1 - dzc)
    # The C++ 'out * (fabsf(x) > dzc)' multiplies by bool (0 or 1)
    return out if abs(x) > dzc else Fraction(0)


# ── Test harness ──────────────────────────────────────────────────────────────

passed = 0
failed = 0


def check(x: Fraction, dz: Fraction, label: str = "") -> None:
    global passed, failed
    lean_out = deadzone_lean(x, dz)
    cpp_out = deadzone_cpp(x, dz)
    if lean_out == cpp_out:
        passed += 1
    else:
        tag = f" [{label}]" if label else ""
        print(f"MISMATCH{tag}: deadzone({x}, {dz})")
        print(f"  Lean: {lean_out}")
        print(f"  C++:  {cpp_out}")
        failed += 1


# ── Test suite ────────────────────────────────────────────────────────────────

print("Running deadzone correspondence tests...\n")

# 1. Zero deadzone: deadzone(x, 0) = x  (no_dz identity)
print("1. Zero deadzone (identity)")
for num in range(-10, 11):
    x = Fraction(num, 10)
    check(x, Fraction(0), f"no_dz x={x}")

# 2. Input inside deadzone: deadzone(x, dz) = 0 when |x| ≤ dz
print("2. Input inside deadzone (output = 0)")
for dz_num in [1, 2, 3, 5]:
    dz = Fraction(dz_num, 10)
    for x_num in range(-dz_num, dz_num + 1):
        x = Fraction(x_num, 10)
        check(x, dz, f"inside dz={dz}, x={x}")

# 3. Positive branch: x > dz, dz ≥ 0
print("3. Positive branch (x > dz)")
for dz_num in [0, 1, 2, 3, 5, 9]:
    dz = Fraction(dz_num, 10)
    for x_num in range(dz_num + 1, 11):
        x = Fraction(x_num, 10)
        check(x, dz, f"pos branch dz={dz}, x={x}")

# 4. Negative branch: x < -dz, dz ≥ 0
print("4. Negative branch (x < -dz)")
for dz_num in [0, 1, 2, 3, 5, 9]:
    dz = Fraction(dz_num, 10)
    for x_num in range(-10, -dz_num):
        x = Fraction(x_num, 10)
        check(x, dz, f"neg branch dz={dz}, x={x}")

# 5. Boundary: x = 1, any dz (at_max)
print("5. Boundary x=1 (at_max)")
for dz_num in range(0, 10):
    dz = Fraction(dz_num, 10)
    check(Fraction(1), dz, f"at_max dz={dz}")

# 6. Boundary: x = -1, any dz (at_min)
print("6. Boundary x=-1 (at_min)")
for dz_num in range(0, 10):
    dz = Fraction(dz_num, 10)
    check(Fraction(-1), dz, f"at_min dz={dz}")

# 7. Odd symmetry: deadzone(-x, dz) = -deadzone(x, dz)
print("7. Odd symmetry")
for x_num in range(0, 11):
    x = Fraction(x_num, 10)
    for dz_num in range(0, 10):
        dz = Fraction(dz_num, 10)
        lean_pos = deadzone_lean(x, dz)
        lean_neg = deadzone_lean(-x, dz)
        cpp_pos = deadzone_cpp(x, dz)
        cpp_neg = deadzone_cpp(-x, dz)
        if lean_neg != -lean_pos:
            print(f"ODD SYMMETRY (Lean) violated: x={x}, dz={dz}: "
                  f"deadzone(-x)={lean_neg} != -{lean_pos}")
            failed += 1
        else:
            passed += 1
        if cpp_neg != -cpp_pos:
            print(f"ODD SYMMETRY (C++) violated: x={x}, dz={dz}: "
                  f"deadzone(-x)={cpp_neg} != -{cpp_pos}")
            failed += 1
        else:
            passed += 1

# 8. Monotone in value: if x1 ≤ x2 then deadzone(x1,dz) ≤ deadzone(x2,dz)
print("8. Monotonicity in value")
xs = [Fraction(n, 10) for n in range(-10, 11)]
for dz_num in [0, 2, 5]:
    dz = Fraction(dz_num, 10)
    prev_lean = None
    prev_cpp = None
    for x in xs:
        curr_lean = deadzone_lean(x, dz)
        curr_cpp = deadzone_cpp(x, dz)
        if prev_lean is not None and curr_lean < prev_lean:
            print(f"MONO VIOLATION (Lean) dz={dz}: output decreased at x={x}")
            failed += 1
        else:
            passed += 1
        if prev_cpp is not None and curr_cpp < prev_cpp:
            print(f"MONO VIOLATION (C++) dz={dz}: output decreased at x={x}")
            failed += 1
        else:
            passed += 1
        prev_lean = curr_lean
        prev_cpp = curr_cpp

# 9. Monotone in dz: wider deadzone → smaller or equal output for x > 0
print("9. Monotonicity in dz (positive x)")
for x_num in [3, 5, 7, 10]:
    x = Fraction(x_num, 10)
    dzs = [Fraction(n, 10) for n in range(0, x_num)]
    prev_lean = None
    prev_cpp = None
    for dz in dzs:
        curr_lean = deadzone_lean(x, dz)
        curr_cpp = deadzone_cpp(x, dz)
        if prev_lean is not None and curr_lean > prev_lean:
            print(f"MONO_DZ VIOLATION (Lean) x={x}: output increased at dz={dz}")
            failed += 1
        else:
            passed += 1
        if prev_cpp is not None and curr_cpp > prev_cpp:
            print(f"MONO_DZ VIOLATION (C++) x={x}: output increased at dz={dz}")
            failed += 1
        else:
            passed += 1
        prev_lean = curr_lean
        prev_cpp = curr_cpp

# 10. Dense grid: all (x, dz) in {-1, -0.9, ..., 1} × {0, 0.1, ..., 0.9}
print("10. Dense grid")
for x_num in range(-10, 11):
    for dz_num in range(0, 10):
        x = Fraction(x_num, 10)
        dz = Fraction(dz_num, 10)
        check(x, dz, f"grid x={x}, dz={dz}")

# 11. Rational fractions with odd denominators (1/3, 1/7, etc.)
#     Only use inputs within the valid domain [-1,1] × [0,0.99) so that the
#     C++ constrain calls are identity and the models agree exactly.
print("11. Rational fractions (odd denominators, in-domain)")
for p in [1, 2, 3, 4, 5, 6]:
    for q in [3, 7, 11]:
        x = Fraction(p, q)
        dz = Fraction(1, q)
        if abs(x) <= Fraction(1) and dz < Fraction(99, 100):
            check(x, dz, f"frac x={x}, dz={dz}")
            check(-x, dz, f"frac x={-x}, dz={dz}")
        check(Fraction(0), dz, f"frac x=0, dz={dz}")

# 12. Output range [-1, 1]
print("12. Output range")
for x_num in range(-10, 11):
    for dz_num in range(0, 10):
        x = Fraction(x_num, 10)
        dz = Fraction(dz_num, 10)
        r = deadzone_lean(x, dz)
        if r < Fraction(-1) or r > Fraction(1):
            print(f"RANGE VIOLATION (Lean) x={x}, dz={dz}: output={r}")
            failed += 1
        else:
            passed += 1
        r2 = deadzone_cpp(x, dz)
        if r2 < Fraction(-1) or r2 > Fraction(1):
            print(f"RANGE VIOLATION (C++) x={x}, dz={dz}: output={r2}")
            failed += 1
        else:
            passed += 1

# ── Report ────────────────────────────────────────────────────────────────────

total = passed + failed
print(f"\nTotal test cases: {total}")
if failed == 0:
    print(f"✅ All {total} cases passed — Lean model matches C++ reference exactly")
    sys.exit(0)
else:
    print(f"❌ {failed} FAILED, {passed} passed")
    sys.exit(1)
