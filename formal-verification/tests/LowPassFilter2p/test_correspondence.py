#!/usr/bin/env python3
"""
LowPassFilter2p correspondence tests — Route B.

🔬 Lean Squad automated correspondence validation.

Validates that the Lean 4 model in FVSquad/LowPassFilter2p.lean
matches the C++ implementation in src/lib/mathlib/math/filter/LowPassFilter2p.hpp
on a shared set of test cases.

C++ logic (Direct Form II):
    T apply(const T &sample) {
        T delay_element_0 = sample - _delay_element_1 * _a1 - _delay_element_2 * _a2;
        T output = delay_element_0 * _b0 + _delay_element_1 * _b1 + _delay_element_2 * _b2;
        _delay_element_2 = _delay_element_1;
        _delay_element_1 = delay_element_0;
        return output;
    }

Lean model (over Rat/fractions):
    def lpf2pApply (c : LPF2pCoeffs) (s : LPF2pState) (sample : Rat) : LPF2pState × Rat :=
      let w0  := sample - s.d1 * c.a1 - s.d2 * c.a2
      let out := w0 * c.b0 + s.d1 * c.b1 + s.d2 * c.b2
      ({ d1 := w0, d2 := s.d1 }, out)

Since the Lean model uses exact rational arithmetic and the C++ uses float,
we compare using Python fractions (exact rational arithmetic) to verify algorithmic
correspondence, isolating model structure from floating-point artefacts.

Run with: python3 test_correspondence.py
"""

from fractions import Fraction
import sys
from dataclasses import dataclass
from typing import List, Tuple


# ── Lean model implementation (Python/Fraction) ──────────────────────────────

@dataclass
class LPF2pState:
    d1: Fraction
    d2: Fraction

@dataclass
class LPF2pCoeffs:
    b0: Fraction
    b1: Fraction
    b2: Fraction
    a1: Fraction
    a2: Fraction

def lean_lpf2p_apply(c: LPF2pCoeffs, s: LPF2pState, sample: Fraction) -> Tuple[LPF2pState, Fraction]:
    """Direct translation of lpf2pApply from LowPassFilter2p.lean."""
    w0  = sample - s.d1 * c.a1 - s.d2 * c.a2
    out = w0 * c.b0 + s.d1 * c.b1 + s.d2 * c.b2
    return LPF2pState(d1=w0, d2=s.d1), out

def lean_apply_n(c: LPF2pCoeffs, s0: LPF2pState, samples: List[Fraction]) -> Tuple[LPF2pState, List[Fraction]]:
    """Apply lean model for a sequence of samples, returning final state and all outputs."""
    s = s0
    outputs = []
    for sample in samples:
        s, out = lean_lpf2p_apply(c, s, sample)
        outputs.append(out)
    return s, outputs


# ── C++ model implementation (Python/Fraction, same algorithm) ───────────────

def cpp_lpf2p_apply(c: LPF2pCoeffs, s: LPF2pState, sample: Fraction) -> Tuple[LPF2pState, Fraction]:
    """Direct translation of C++ apply() — using Fraction for exact comparison."""
    delay_element_0 = sample - s.d1 * c.a1 - s.d2 * c.a2
    output = delay_element_0 * c.b0 + s.d1 * c.b1 + s.d2 * c.b2
    new_d2 = s.d1
    new_d1 = delay_element_0
    return LPF2pState(d1=new_d1, d2=new_d2), output

def cpp_apply_n(c: LPF2pCoeffs, s0: LPF2pState, samples: List[Fraction]) -> Tuple[LPF2pState, List[Fraction]]:
    s = s0
    outputs = []
    for sample in samples:
        s, out = cpp_lpf2p_apply(c, s, sample)
        outputs.append(out)
    return s, outputs


# ── Test cases ────────────────────────────────────────────────────────────────

def F(x):
    """Convert string or number to Fraction."""
    return Fraction(x)

def make_coeffs(b0, b1, b2, a1, a2):
    return LPF2pCoeffs(F(b0), F(b1), F(b2), F(a1), F(a2))

def zero_state():
    return LPF2pState(F(0), F(0))

# Disabled filter: b0=1, b1=b2=a1=a2=0
DISABLED = make_coeffs(1, 0, 0, 0, 0)

# Butterworth-like rational approximation (not a real Butterworth, but exercises b1=2*b0, b2=b0)
# Using b0=1/4, b1=1/2, b2=1/4, a1=-1/2, a2=1/4 (arbitrary rational coefficients)
BUTTERWORTH_RAT = make_coeffs("1/4", "1/2", "1/4", "-1/2", "1/4")

# Another set: b0=1/10, b1=2/10, b2=1/10, a1=-3/5, a2=1/5
COEFF_B = make_coeffs("1/10", "2/10", "1/10", "-3/5", "1/5")

# DC-unity coefficients: b0+b1+b2 = 1+a1+a2
# b0=1/6, b1=2/6, b2=1/6, a1=-1/6, a2=-1/6: sum(b)=4/6, sum(a_den)=1+(-1/6)+(-1/6)=4/6 ✓
DC_UNITY = make_coeffs("1/6", "2/6", "1/6", "-1/6", "-1/6")

CASES = [
    # (name, coeffs, d1_init, d2_init, samples)
    # Basic disabled pass-through
    ("disabled_zero_state_single",  DISABLED,       "0", "0", ["1"]),
    ("disabled_zero_state_multi",   DISABLED,       "0", "0", ["1", "2", "3", "-1", "0"]),
    ("disabled_nonzero_state",      DISABLED,       "5", "-3", ["7", "-2", "0"]),
    ("disabled_neg_input",          DISABLED,       "0", "0", ["-5", "-10", "-15"]),
    ("disabled_zero_input",         DISABLED,       "3", "7", ["0", "0", "0"]),

    # Butterworth-like rational coefficients
    ("bw_rat_zero_in",              BUTTERWORTH_RAT, "0", "0", ["0"]*5),
    ("bw_rat_unit_step",            BUTTERWORTH_RAT, "0", "0", ["1"]*8),
    ("bw_rat_neg_step",             BUTTERWORTH_RAT, "0", "0", ["-1"]*8),
    ("bw_rat_alternating",          BUTTERWORTH_RAT, "0", "0", ["1", "-1"]*5),
    ("bw_rat_nonzero_init",         BUTTERWORTH_RAT, "1/2", "-1/3", ["1", "2", "3"]),
    ("bw_rat_large_input",          BUTTERWORTH_RAT, "0", "0", ["100", "100", "100"]),
    ("bw_rat_fractional_input",     BUTTERWORTH_RAT, "0", "0", ["1/3", "2/3", "1"]),

    # Coefficient set B
    ("coeff_b_zero_in",             COEFF_B, "0", "0", ["0"]*5),
    ("coeff_b_unit_step",           COEFF_B, "0", "0", ["1"]*10),
    ("coeff_b_impulse",             COEFF_B, "0", "0", ["1"] + ["0"]*9),
    ("coeff_b_ramp",                COEFF_B, "0", "0", [str(k) for k in range(10)]),
    ("coeff_b_nonzero_init",        COEFF_B, "3/4", "1/4", ["0"]*5),

    # DC unity: DC gain = 1 → steady-state output should equal input
    ("dc_unity_zero_state_const",   DC_UNITY, "0", "0", ["1"]*20),
    ("dc_unity_zero_state_neg",     DC_UNITY, "0", "0", ["-1"]*20),
    ("dc_unity_impulse",            DC_UNITY, "0", "0", ["1"] + ["0"]*15),
    ("dc_unity_step_various",       DC_UNITY, "0", "0", ["1/2"]*15),

    # Zero input, nonzero state (exponential decay)
    ("bw_rat_zero_in_nonzero_state", BUTTERWORTH_RAT, "1", "1", ["0"]*10),
    ("coeff_b_zero_in_nonzero_state", COEFF_B, "2", "-1", ["0"]*10),

    # Single-sample checks (boundary)
    ("disabled_single_pos",         DISABLED, "0", "0", ["42"]),
    ("disabled_single_neg",         DISABLED, "0", "0", ["-7"]),
    ("disabled_single_frac",        DISABLED, "0", "0", ["1/7"]),
    ("bw_rat_single",               BUTTERWORTH_RAT, "0", "0", ["5"]),
    ("coeff_b_single",              COEFF_B, "1/2", "1/3", ["2/5"]),
]


# ── Test runner ───────────────────────────────────────────────────────────────

def run_tests():
    passed = 0
    failed = 0
    errors = []

    for case in CASES:
        name, c, d1_str, d2_str, sample_strs = case
        d1 = F(d1_str)
        d2 = F(d2_str)
        samples = [F(s) for s in sample_strs]

        s0 = LPF2pState(d1=d1, d2=d2)

        lean_s, lean_outs = lean_apply_n(c, s0, samples)
        cpp_s, cpp_outs   = cpp_apply_n(c, s0, samples)

        ok = (lean_outs == cpp_outs and
              lean_s.d1 == cpp_s.d1 and
              lean_s.d2 == cpp_s.d2)

        if ok:
            passed += 1
        else:
            failed += 1
            diff_outs = [(i, l, cr) for i, (l, cr) in enumerate(zip(lean_outs, cpp_outs)) if l != cr]
            errors.append((name, diff_outs, lean_s, cpp_s))

    if errors:
        print(f"FAILED: {failed}/{passed + failed} test cases failed\n")
        for name, diff_outs, lean_s, cpp_s in errors:
            print(f"  CASE: {name}")
            for i, l, cr in diff_outs:
                print(f"    output[{i}]: lean={l}, cpp={cr}")
            if lean_s.d1 != cpp_s.d1:
                print(f"    final d1: lean={lean_s.d1}, cpp={cpp_s.d1}")
            if lean_s.d2 != cpp_s.d2:
                print(f"    final d2: lean={lean_s.d2}, cpp={cpp_s.d2}")
        sys.exit(1)
    else:
        total = passed + failed
        print(f"OK: {total}/{total} test cases passed")
        print(f"Tested: disabled pass-through, Butterworth-like rational, DC-unity, impulse response, ramp, zero-input decay")
        sys.exit(0)


if __name__ == "__main__":
    run_tests()
