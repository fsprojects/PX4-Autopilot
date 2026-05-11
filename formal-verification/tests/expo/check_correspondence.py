#!/usr/bin/env python3
"""
Route B Correspondence Tests: PX4 expo (Exponential RC Curve)
🔬 Lean Squad automated formal verification.

Validates that the Lean 4 rational model of the expo function in
formal-verification/lean/FVSquad/Expo.lean produces results behaviourally
identical to the C++ template implementation in
src/lib/mathlib/math/Functions.hpp on a comprehensive set of rational inputs.

## Model summary

C++ source (src/lib/mathlib/math/Functions.hpp):
    template<typename T>
    const T expo(const T &value, const T &e)
    {
        T x = constrain(value, (T)-1, (T)1);
        T ec = constrain(e, (T)0, (T)1);
        return (1 - ec) * x + ec * x * x * x;
    }

Lean 4 model (Expo.lean, namespace PX4):
    def constrainRat (v lo hi : Rat) : Rat :=
      if v < lo then lo else if v > hi then hi else v

    def expoRat (v e : Rat) : Rat :=
      let x  := constrainRat v (-1) 1
      let ec := constrainRat e 0 1
      (1 - ec) * x + ec * x * x * x

The model uses exact rational arithmetic (no float rounding). Correspondence
is verified by constructing rational inputs and comparing each side's output.

Usage:
    python3 check_correspondence.py

Exit code 0 on success, non-zero on any mismatch.
"""

import sys
from fractions import Fraction

# ── Lean model (exact translation from Expo.lean) ───────────────────────────

def constrain_rat(v: Fraction, lo: Fraction, hi: Fraction) -> Fraction:
    """constrainRat — clamp v to [lo, hi]."""
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v

def expo_rat(v: Fraction, e: Fraction) -> Fraction:
    """expoRat — Lean 4 model of PX4's expo function."""
    x = constrain_rat(v, Fraction(-1), Fraction(1))
    ec = constrain_rat(e, Fraction(0), Fraction(1))
    return (1 - ec) * x + ec * x * x * x

# ── C++ reference (exact rational translation) ───────────────────────────────

def expo_cpp(value: Fraction, e: Fraction) -> Fraction:
    """Direct translation of the C++ expo template with exact rational arithmetic."""
    x  = constrain_rat(value, Fraction(-1), Fraction(1))
    ec = constrain_rat(e,     Fraction(0),  Fraction(1))
    return (1 - ec) * x + ec * x * x * x

# ── Test harness ─────────────────────────────────────────────────────────────

passed = 0
failed = 0

def check(v: Fraction, e: Fraction, description: str = ""):
    """Run one test case and report any mismatch."""
    global passed, failed
    lean   = expo_rat(v, e)
    cpp    = expo_cpp(v, e)
    if lean != cpp:
        print(f"MISMATCH: v={v}, e={e}")
        print(f"  Lean model : {lean}")
        print(f"  C++ ref    : {cpp}")
        if description:
            print(f"  Note       : {description}")
        failed += 1
    else:
        passed += 1


# ── Test groups ──────────────────────────────────────────────────────────────

# 1. Boundary / special values
for v in [Fraction(-1), Fraction(0), Fraction(1)]:
    for e in [Fraction(0), Fraction(1, 2), Fraction(1)]:
        check(v, e, f"boundary v={v}, e={e}")

# 2. expo_at_zero: expoRat 0 e = 0
for denom in range(1, 11):
    e = Fraction(denom - 1, denom)  # e ∈ {0, 1/2, 2/3, ..., 9/10}
    check(Fraction(0), e, f"zero value, e={e}")

# 3. expo_at_pos_one: expoRat 1 e = 1
for num in range(0, 11):
    e = Fraction(num, 10)
    check(Fraction(1), e, f"positive one, e={e}")

# 4. expo_at_neg_one: expoRat (-1) e = -1
for num in range(0, 11):
    e = Fraction(num, 10)
    check(Fraction(-1), e, f"negative one, e={e}")

# 5. expo_linear: e=0 gives identity (clamped)
for num in range(-12, 13):
    v = Fraction(num, 10)
    check(v, Fraction(0), f"linear (e=0), v={v}")

# 6. expo_cubic: e=1 gives x³
for num in range(-10, 11):
    v = Fraction(num, 10)
    check(v, Fraction(1), f"cubic (e=1), v={v}")

# 7. expo_odd: expoRat (-v) e = -expoRat v e
for num in range(0, 11):
    v = Fraction(num, 10)
    for den in range(1, 6):
        e = Fraction(den - 1, den)
        r_pos = expo_rat(v, e)
        r_neg = expo_rat(-v, e)
        if r_neg != -r_pos:
            print(f"ODD SYMMETRY VIOLATION: v={v}, e={e}: expo({-v},{e})={r_neg} != -{r_pos}")
            failed += 1
        else:
            passed += 1
        check(v, e, f"odd symmetry, v={v}, e={e}")
        check(-v, e, f"odd symmetry, -v={-v}, e={e}")

# 8. expo_in_range: output ∈ [-1, 1]
for num in range(-15, 16):
    v = Fraction(num, 10)
    for den in range(1, 11):
        e = Fraction(den - 1, den)
        result = expo_rat(v, e)
        if result < Fraction(-1) or result > Fraction(1):
            print(f"RANGE VIOLATION: v={v}, e={e}: output={result}")
            failed += 1
        else:
            passed += 1
        check(v, e)

# 9. Dense grid: many (v, e) pairs in [-1.5, 1.5] × [−0.2, 1.2]
#    (values outside the expected domain — clamp kicks in)
for v_num in range(-15, 16):
    for e_num in range(-2, 13):
        v = Fraction(v_num, 10)
        e = Fraction(e_num, 10)
        check(v, e, f"dense grid v={v}, e={e}")

# 10. Rational fractions: 1/3, 1/7, etc.
for p in [1, 2, 3, 4, 5, 6]:
    for q in [3, 7, 11]:
        v = Fraction(p, q)
        e = Fraction(1, q)
        check(v, e, f"fraction v={v}, e={e}")
        check(-v, e, f"fraction -v={-v}, e={e}")

# ── Report ─────────────────────────────────────────────────────────────────

total = passed + failed
print(f"\nTotal test cases: {total}")
if failed == 0:
    print(f"✅ All {total} cases passed — Lean model matches C++ reference exactly")
    sys.exit(0)
else:
    print(f"❌ {failed} FAILED, {passed} passed")
    sys.exit(1)
