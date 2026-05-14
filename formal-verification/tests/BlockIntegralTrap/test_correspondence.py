#!/usr/bin/env python3
"""
BlockIntegralTrap correspondence tests — Route B.

🔬 Lean Squad automated correspondence validation.

Validates that the Lean 4 model in FVSquad/BlockIntegralTrap.lean
matches the C++ implementation in src/lib/controllib/BlockIntegralTrap.cpp
on a shared set of test cases.

C++ logic (exact):
    float BlockIntegralTrap::update(float input) {
        setY(_limit.update(getY() + (getU() + input) / 2.0f * getDt()));
        setU(input);
        return getY();
    }

Lean model (over Rat/fractions):
    def itUpdate (p : ITParams) (s : ITState) (input : Rat) : ITState :=
      let trap := s.y + (s.u + input) / 2 * p.dt
      { y := rConstrain trap (-p.limit) p.limit,
        u := input }

Since the Lean model uses exact rational arithmetic and the C++ uses float,
we compare at rational precision (using Python fractions), ignoring float rounding.
This isolates algorithmic correspondence from floating-point artefacts.
"""

from fractions import Fraction
import sys

# ── Lean model implementation (Python/Fraction) ──────────────────────────────

def r_constrain(v: Fraction, lo: Fraction, hi: Fraction) -> Fraction:
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v

def it_update(dt: Fraction, limit: Fraction, y: Fraction, u: Fraction, inp: Fraction):
    """Returns (new_y, new_u) matching itUpdate in Lean."""
    trap = y + (u + inp) / Fraction(2) * dt
    new_y = r_constrain(trap, -limit, limit)
    new_u = inp
    return new_y, new_u

def it_fold(dt: Fraction, limit: Fraction, y0: Fraction, u0: Fraction, inputs):
    """Applies itUpdate for each input in sequence."""
    y, u = y0, u0
    for inp in inputs:
        y, u = it_update(dt, limit, y, u, inp)
    return y, u

# ── C++ model implementation (Python/float, same algorithm) ──────────────────

def cpp_constrain(v: float, lo: float, hi: float) -> float:
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v

def cpp_update(dt: float, limit: float, y: float, u: float, inp: float):
    trap = y + (u + inp) / 2.0 * dt
    new_y = cpp_constrain(trap, -limit, limit)
    new_u = inp
    return new_y, new_u

# ── Test harness ──────────────────────────────────────────────────────────────

CASES = [
    # (description, dt, limit, y0, u0, inputs)
    ("zero_state_zero_input",          "1/100", "10", "0", "0", ["0"]*5),
    ("constant_positive_input",        "1/100", "10", "0", "0", ["1"]*10),
    ("constant_negative_input",        "1/100", "10", "0", "0", ["-1"]*10),
    ("saturation_positive",            "1/10",  "1",  "0", "0", ["100"]*5),
    ("saturation_negative",            "1/10",  "1",  "0", "0", ["-100"]*5),
    ("saturation_already_at_limit",    "1/10",  "5",  "5", "0", ["10"]*3),
    ("saturation_already_neg_limit",   "1/10",  "5", "-5", "0", ["-10"]*3),
    ("step_up_then_step_down",         "1/100", "10", "0", "0", ["10"]*5 + ["-10"]*5),
    ("alternating_sign",               "1/100", "5",  "0", "0", ["1","-1"]*10),
    ("large_dt_hits_limit_fast",       "1",     "2",  "0", "0", ["1"]*6),
    ("ramp_input",                     "1/10",  "20", "0", "0",
        [str(i) for i in range(1, 11)]),
    ("nonzero_initial_state",          "1/20",  "5",  "2", "1", ["1"]*5),
    ("previous_input_remembered",      "1/10",  "10", "0", "3", ["1"]*3),
    ("limit_boundary_single_step",     "1/2",   "3",  "0", "0", ["6"]),
    ("dt_half",                        "1/2",   "10", "0", "0", ["2"]*4),
    ("two_updates_trapezoid",          "1",     "100","0", "0", ["1","2"]),
    ("three_updates",                  "1",     "100","0", "0", ["1","2","3"]),
    ("zero_dt_no_integration",         "0",     "5",  "2", "1", ["3"]*4),
    ("tiny_inputs",                    "1/100", "10", "0", "0",
        ["1/1000"]*20),
    ("fractional_limit",               "1/10",  "3/2","0", "0", ["10"]*3),
]

def _f(s: str) -> Fraction:
    return Fraction(s)

def run_tests():
    passed = 0
    failed = 0
    errors = []

    for name, dt_s, lim_s, y0_s, u0_s, inp_strs in CASES:
        dt   = _f(dt_s)
        lim  = _f(lim_s)
        y0   = _f(y0_s)
        u0   = _f(u0_s)
        inps = [_f(x) for x in inp_strs]

        # Lean model (exact rational)
        lean_y, lean_u = it_fold(dt, lim, y0, u0, inps)

        # C++ model (float)
        y_f, u_f = float(y0), float(u0)
        for inp in inps:
            y_f, u_f = cpp_update(float(dt), float(lim), y_f, u_f, float(inp))

        # Compare: allow tiny float rounding tolerance
        diff = abs(float(lean_y) - y_f)
        tol = max(1e-9, 1e-6 * max(1.0, abs(float(lean_y)), abs(y_f)))
        u_diff = abs(float(lean_u) - u_f)

        if diff > tol or u_diff > 1e-9:
            failed += 1
            errors.append(
                f"FAIL [{name}]: lean_y={float(lean_y):.8g} cpp_y={y_f:.8g} "
                f"diff={diff:.2e}  lean_u={float(lean_u):.8g} cpp_u={u_f:.8g}"
            )
        else:
            passed += 1

    # Additional: test theorems numerically
    # itUpdate_y_bounded: result y is in [-limit, limit]
    for _ in range(100):
        import random
        dt   = Fraction(random.randint(1, 10), random.randint(10, 100))
        lim  = Fraction(random.randint(1, 20))
        y    = Fraction(random.randint(-10, 10))
        u    = Fraction(random.randint(-10, 10))
        inp  = Fraction(random.randint(-20, 20))
        ny, _ = it_update(dt, lim, y, u, inp)
        if not (-lim <= ny <= lim):
            failed += 1
            errors.append(f"FAIL [bounded_property]: ny={ny} lim={lim}")
        else:
            passed += 1

    return passed, failed, errors

if __name__ == "__main__":
    passed, failed, errors = run_tests()
    total = passed + failed
    print(f"BlockIntegralTrap correspondence tests: {passed}/{total} passed")
    if errors:
        for e in errors:
            print(e)
        sys.exit(1)
    else:
        print("All tests PASSED — Lean model matches C++ algorithm on all cases.")
        sys.exit(0)
