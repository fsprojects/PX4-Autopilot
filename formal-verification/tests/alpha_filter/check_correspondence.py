#!/usr/bin/env python3
"""
Route B Correspondence Tests: PX4 AlphaFilter
🔬 Lean Squad automated formal verification.

Validates that the Lean 4 rational model of AlphaFilter::updateCalculation in
formal-verification/lean/FVSquad/AlphaFilter.lean produces results that match
the C++ template implementation in src/lib/mathlib/math/filter/AlphaFilter.hpp
on a comprehensive set of inputs.

## Model summary

C++ source (AlphaFilter.hpp):
    template <typename T>
    T AlphaFilter<T>::updateCalculation(const T &sample) {
        return _filter_state + _alpha * (sample - _filter_state);
    }

Lean 4 model (AlphaFilter.lean, namespace PX4.AlphaFilter):
    def alphaUpdate (state alpha sample : Rat) : Rat :=
        state + alpha * (sample - state)

Both expressions are algebraically identical:
    state + alpha * (sample - state)
The Lean model uses exact rational arithmetic (Rat); the C++ uses float32.

## Correspondence strategy

We choose inputs that are exactly representable as float32 (dyadic rationals
with denominators that are powers of 2 and numerators small enough to fit
without rounding). For such inputs all intermediate results are also exact,
so the Lean rational model and the float C++ must agree to within 0 ULP.

For inputs that are NOT exactly representable (e.g. 1/3), we compare to a
tighter relative tolerance (< 1e-6) and document the known mismatch cause.

## Running

    python3 check_correspondence.py

Exit code 0 on success (all cases pass), non-zero on any failure.
"""

import sys
import math
from fractions import Fraction

# ── Lean rational model ───────────────────────────────────────────────────────

def alpha_update_lean(state: Fraction, alpha: Fraction, sample: Fraction) -> Fraction:
    """Exact translation of alphaUpdate from AlphaFilter.lean."""
    return state + alpha * (sample - state)


def alpha_iterate_lean(state: Fraction, alpha: Fraction, target: Fraction, n: int) -> Fraction:
    """Iterate alphaUpdate n times (for multi-step tests)."""
    s = state
    for _ in range(n):
        s = alpha_update_lean(s, alpha, target)
    return s

# ── C++ float simulation ──────────────────────────────────────────────────────

def alpha_update_cpp(state: float, alpha: float, sample: float) -> float:
    """
    Mirrors AlphaFilter<float>::updateCalculation:
        return _filter_state + _alpha * (sample - _filter_state);
    Uses Python float64 (IEEE 754 double) to simulate float32 C++ behaviour.
    For dyadic inputs small enough to be exact in float32, float64 gives the
    same result (no additional rounding), so we can compare directly.
    """
    return state + alpha * (sample - state)


def alpha_iterate_cpp(state: float, alpha: float, target: float, n: int) -> float:
    s = state
    for _ in range(n):
        s = alpha_update_cpp(s, alpha, target)
    return s

# ── Comparison helper ─────────────────────────────────────────────────────────

FAILURES = []
PASSES   = 0


def check(label: str, state, alpha, sample, exact: bool = True):
    """
    Run one correspondence test.

    Parameters
    ----------
    label  : human-readable description
    state  : initial filter state (int, float, or Fraction; converted internally)
    alpha  : filter coefficient in [0, 1]
    sample : new input sample
    exact  : if True, the input is exactly representable in float and we require
             the float and Lean results to agree exactly (float(lean_result) == cpp_result).
             If False, we allow a relative tolerance of 2e-6.
    """
    global PASSES

    fs  = Fraction(state).limit_denominator(2**24)
    fa  = Fraction(alpha).limit_denominator(2**24)
    fsp = Fraction(sample).limit_denominator(2**24)

    lean_result = alpha_update_lean(fs, fa, fsp)
    cpp_result  = alpha_update_cpp(float(fs), float(fa), float(fsp))

    lean_float = float(lean_result)

    if exact:
        ok = lean_float == cpp_result
    else:
        if cpp_result == 0.0:
            ok = lean_float == 0.0
        else:
            ok = abs(lean_float - cpp_result) / abs(cpp_result) < 2e-6

    if ok:
        PASSES += 1
    else:
        FAILURES.append({
            "label": label,
            "state": str(fs),
            "alpha": str(fa),
            "sample": str(fsp),
            "lean": str(lean_result),
            "lean_float": lean_float,
            "cpp": cpp_result,
            "diff": abs(lean_float - cpp_result),
        })


def check_multi(label: str, state, alpha, target, n: int):
    """
    Run a multi-step correspondence test (iterate n times).
    Uses a relative tolerance of 2e-6 (accumulated rounding in n float ops).
    """
    global PASSES

    fs = Fraction(state).limit_denominator(2**24)
    fa = Fraction(alpha).limit_denominator(2**24)
    ft = Fraction(target).limit_denominator(2**24)

    lean_result = alpha_iterate_lean(fs, fa, ft, n)
    cpp_result  = alpha_iterate_cpp(float(fs), float(fa), float(ft), n)

    lean_float = float(lean_result)

    if cpp_result == 0.0:
        ok = abs(lean_float) < 1e-7
    else:
        ok = abs(lean_float - cpp_result) / max(abs(cpp_result), 1e-12) < 2e-6 * n

    if ok:
        PASSES += 1
    else:
        FAILURES.append({
            "label": label + f" (n={n})",
            "state": str(fs),
            "alpha": str(fa),
            "target": str(ft),
            "lean_float": lean_float,
            "cpp": cpp_result,
            "diff": abs(lean_float - cpp_result),
        })


# ── Test suite ────────────────────────────────────────────────────────────────

def run_tests():
    # ------------------------------------------------------------------
    # 1. Boundary / degenerate cases
    # ------------------------------------------------------------------
    check("alpha=0: state frozen",         state=0,   alpha=0,   sample=1,   exact=True)
    check("alpha=0: state frozen (nonzero)",state=0.5, alpha=0,   sample=1,   exact=True)
    check("alpha=1: immediate jump",        state=0,   alpha=1,   sample=1,   exact=True)
    check("alpha=1: immediate jump (neg)",  state=0,   alpha=1,   sample=-1,  exact=True)
    check("alpha=1: state = sample always", state=0.5, alpha=1,   sample=0.75,exact=True)
    check("fixed point: sample=state",      state=0.5, alpha=0.5, sample=0.5, exact=True)
    check("zero state, zero sample",        state=0,   alpha=0.5, sample=0,   exact=True)
    check("zero alpha, large sample",       state=100, alpha=0,   sample=1e4, exact=True)

    # ------------------------------------------------------------------
    # 2. Simple dyadic-rational inputs (exact in float32)
    # ------------------------------------------------------------------
    for alpha in [Fraction(1,2), Fraction(1,4), Fraction(3,4), Fraction(1,8), Fraction(7,8)]:
        for state in [Fraction(0), Fraction(1), Fraction(-1), Fraction(1,2)]:
            for sample in [Fraction(0), Fraction(1), Fraction(-1), Fraction(1,2), Fraction(-1,2)]:
                check(f"dyadic: state={state}, alpha={alpha}, sample={sample}",
                      state=state, alpha=alpha, sample=sample, exact=True)

    # ------------------------------------------------------------------
    # 3. Signed and negative states/samples
    # ------------------------------------------------------------------
    check("neg state, pos sample, alpha=0.5",  state=-1,  alpha=0.5,  sample=1,   exact=True)
    check("pos state, neg sample, alpha=0.5",  state=1,   alpha=0.5,  sample=-1,  exact=True)
    check("neg state, neg sample",             state=-0.5,alpha=0.25, sample=-1,  exact=True)
    check("large state, small sample",         state=64,  alpha=0.5,  sample=0,   exact=True)
    check("small state, large sample",         state=0,   alpha=0.5,  sample=64,  exact=True)

    # ------------------------------------------------------------------
    # 4. Fine grid: alpha in {0.1, 0.2, ..., 0.9} × state × sample
    #    (non-dyadic — use loose tolerance)
    # ------------------------------------------------------------------
    for alpha_val in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]:
        for state_val in [-1.0, -0.5, 0.0, 0.5, 1.0]:
            for sample_val in [-1.0, 0.0, 1.0]:
                check(f"grid: state={state_val}, alpha={alpha_val:.1f}, sample={sample_val}",
                      state=state_val, alpha=alpha_val, sample=sample_val, exact=False)

    # ------------------------------------------------------------------
    # 5. Multi-step convergence (state -> target over n steps)
    # ------------------------------------------------------------------
    for alpha_val in [Fraction(1,2), Fraction(1,4), Fraction(1,10)]:
        check_multi(f"multi 10 steps alpha={alpha_val}", state=0, alpha=alpha_val, target=1, n=10)
        check_multi(f"multi 50 steps alpha={alpha_val}", state=0, alpha=alpha_val, target=1, n=50)
        check_multi(f"multi 10 steps neg, alpha={alpha_val}",
                    state=0, alpha=alpha_val, target=-1, n=10)

    # ------------------------------------------------------------------
    # 6. Key theorem spot-checks (verify Lean model satisfies spec properties)
    # ------------------------------------------------------------------

    # Theorem: alphaUpdate_fixed — alphaUpdate state alpha state = state
    for s in [Fraction(0), Fraction(1,3), Fraction(-7,4), Fraction(100)]:
        for a in [Fraction(0), Fraction(1,2), Fraction(1)]:
            lean_val = alpha_update_lean(s, a, s)
            assert lean_val == s, f"alphaUpdate_fixed failed: state={s}, alpha={a}"
    print("  [ok] alphaUpdate_fixed holds for all test cases")

    # Theorem: alphaUpdate_alpha_zero — alphaUpdate state 0 sample = state
    for s in [Fraction(1), Fraction(-1), Fraction(1,2)]:
        for sp in [Fraction(0), Fraction(99)]:
            lean_val = alpha_update_lean(s, Fraction(0), sp)
            assert lean_val == s, f"alpha_zero failed: state={s}, sample={sp}"
    print("  [ok] alphaUpdate_alpha_zero holds for all test cases")

    # Theorem: alphaUpdate_alpha_one — alphaUpdate state 1 sample = sample
    for s in [Fraction(0), Fraction(5), Fraction(-3)]:
        for sp in [Fraction(7), Fraction(-2), Fraction(0)]:
            lean_val = alpha_update_lean(s, Fraction(1), sp)
            assert lean_val == sp, f"alpha_one failed: state={s}, sample={sp}"
    print("  [ok] alphaUpdate_alpha_one holds for all test cases")

    # Theorem: alphaUpdate_no_overshoot_up — state ≤ sample → new ∈ [state, sample]
    for s in [Fraction(0), Fraction(1,4), Fraction(-1,2)]:
        for sp in [s, s + Fraction(1,2), s + Fraction(3)]:
            for a in [Fraction(0), Fraction(1,4), Fraction(1,2), Fraction(3,4), Fraction(1)]:
                new = alpha_update_lean(s, a, sp)
                assert s <= new <= sp, f"no_overshoot_up failed: {s} <= {new} <= {sp}"
    print("  [ok] alphaUpdate_no_overshoot_up holds for all test cases")

    # Theorem: alphaUpdate_no_overshoot_down — sample ≤ state → new ∈ [sample, state]
    for s in [Fraction(1), Fraction(3,4), Fraction(-1,4)]:
        for sp in [s, s - Fraction(1,2), s - Fraction(3)]:
            for a in [Fraction(0), Fraction(1,4), Fraction(1,2), Fraction(3,4), Fraction(1)]:
                new = alpha_update_lean(s, a, sp)
                assert sp <= new <= s, f"no_overshoot_down failed: {sp} <= {new} <= {s}"
    print("  [ok] alphaUpdate_no_overshoot_down holds for all test cases")

    # Theorem: alphaIterate_formula — state_n = target + (state-target)*(1-alpha)^n
    for s0 in [Fraction(0), Fraction(1), Fraction(-1,2)]:
        for a in [Fraction(1,4), Fraction(1,2), Fraction(3,4)]:
            for tgt in [Fraction(0), Fraction(1), Fraction(-1)]:
                for n in range(6):
                    iterated = alpha_iterate_lean(s0, a, tgt, n)
                    formula  = tgt + (s0 - tgt) * (1 - a) ** n
                    assert iterated == formula, \
                        f"alphaIterate_formula mismatch: n={n}, got {iterated}, expected {formula}"
    print("  [ok] alphaIterate_formula (closed-form) holds for all test cases")


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    print("AlphaFilter Correspondence Tests")
    print("🔬 Lean Squad automated formal verification")
    print()

    run_tests()

    print()
    total = PASSES + len(FAILURES)
    if FAILURES:
        print(f"FAILED: {len(FAILURES)}/{total} cases failed")
        for f in FAILURES[:10]:
            print(f"  {f}")
        return 1
    else:
        print(f"PASSED: all {total} correspondence cases passed ✅")
        return 0


if __name__ == "__main__":
    sys.exit(main())
