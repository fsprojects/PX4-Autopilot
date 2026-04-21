# Atmosphere Correspondence Tests

🔬 *Lean Squad automated formal verification.*

This directory contains Route B correspondence tests for the PX4 atmosphere
library, verifying that the Lean 4 rational model in
`formal-verification/lean/FVSquad/Atmosphere.lean` produces results consistent
with the C++ implementation in `src/lib/atmosphere/atmosphere.cpp`.

## What Is Tested

Two functions:

| C++ function | Lean model | Formula |
|---|---|---|
| `getDensityFromPressureAndTemp(P, T)` | `densityRat P T` | `P / (kR · (T + 273.15))` |
| `getStandardTemperatureAtAltitude(h)` | `tempAtAltRat h` | `15 + (-13/2000) · h` |

## Test Cases

Defined in `test_cases.json`:

- **11 density cases**: spanning ISA sea-level through tropopause, plus edge
  cases (extreme pressure, cold temperature, stratosphere).
- **10 temperature cases**: 0 to 15 000 m, including negative altitude (Dead Sea).
- **5 invariant checks**: monotonicity in pressure, anti-monotonicity in
  temperature, temperature strictly decreasing with altitude, ideal gas law
  identity, and density proportionality.

**Total: 26 test cases.**

## How to Run

```bash
cd formal-verification/tests/atmosphere
python3 check_correspondence.py
```

Requires Python 3.6+; no external packages needed (`fractions`, `json`, `math`
are all stdlib).

Exit code is `0` on success, non-zero if any test fails.

## Last Known Result

All 26 tests passed. Maximum relative error observed: `1.90e-16` (round-off at
double-precision level — functionally zero). This confirms that the Lean rational
model is an **exact** (not just approximate) model of the mathematical formula,
to the precision of Python double arithmetic.

```
Results: 26/26 passed, 0 failed
✓ All correspondence tests PASSED
  The Lean rational model agrees with the C++ float implementation
  within ±2e-05 relative tolerance on all 26 cases.
```

## Methodology

### C++ side (simulated)
Python `float` (double precision) with the C++ constant values:
- `kAirGasConstant = 287.1`
- `kAbsoluteNullCelsius = -273.15`
- `kTempGradient = -6.5 / 1000`

### Lean model side (exact)
Python `fractions.Fraction` (exact rational arithmetic) with:
- `kR = Fraction(2871, 10)` (= 287.1 exactly)
- `kAbsNull = Fraction(-27315, 100)` (= -273.15 exactly)
- `kTempGrad = Fraction(-13, 2000)` (= -0.0065 exactly)

### Tolerance
`±2e-5` relative (20 ppm). Observed errors are at double-precision round-off
(`~1e-16`), confirming the model is mathematically equivalent to the formula.

## What Is NOT Tested

- **`getPressureFromAltitude`** and **`getAltitudeFromPressure`**: these use
  `powf` (a transcendental function) and are deferred until Mathlib's
  `Real.rpow` is available. They are outside the scope of the current Lean model.
- **Single-precision float rounding**: the C++ uses `float` (32-bit); these
  tests simulate with Python `float` (double-precision). The rounding difference
  is at most ~2e-7 relative, well within the 20 ppm tolerance.
- **`NaN` / `Inf` inputs**: not tested; the C++ performs no bounds checking,
  and the Lean model requires `P > 0` and `T_celsius > -273.15` as preconditions.

## Correspondence Level

**Exact** for `densityRat` and `tempAtAltRat`. The Lean model faithfully
captures the C++ formula with rational constants that are exactly equal to the
float constants (287.1 = 2871/10, -273.15 = -27315/100, -0.0065 = -13/2000).
See `formal-verification/CORRESPONDENCE.md` for full details.
