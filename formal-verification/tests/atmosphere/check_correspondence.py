#!/usr/bin/env python3
"""
Correspondence test: PX4 atmosphere library C++ implementation vs Lean model.

🔬 Lean Squad automated formal verification.

This script verifies that the Lean 4 rational model in
`formal-verification/lean/FVSquad/Atmosphere.lean` agrees with the
C++ implementation in `src/lib/atmosphere/atmosphere.cpp` on shared
test cases from `test_cases.json`.

## Approach

- **C++ side**: simulated using Python `float` (IEEE 754 single-precision
  semantics are approximated; Python uses double precision, so we track the
  known constant values from the C++ source exactly).
- **Lean model side**: computed using Python `fractions.Fraction` (exact
  rational arithmetic), mirroring the `Rat`-based Lean definitions.

## Correspondence checked

1. `getDensityFromPressureAndTemp(P, T_celsius)` vs `densityRat(P, T_celsius)`
2. `getStandardTemperatureAtAltitude(h)` vs `tempAtAltRat(h)`

## Tolerances

C++ uses `float` (32-bit, ~7 decimal digits). The Lean model uses exact
rational arithmetic with `kR = 2871/10` (vs C++ `287.1f`) and
`kTempGrad = -13/2000` (vs C++ `-6.5f/1000.f`).

The tolerance is set at `2e-5` relative (20 ppm), which is tight enough to
catch model divergences but loose enough to accommodate the known difference
between the float constants and their rational approximations.

Run:
    python3 check_correspondence.py

Exit code 0 on success; non-zero on failure.
"""

import json
import math
import sys
from fractions import Fraction

# ─── C++ constants (from atmosphere.h, as Python floats) ─────────────────────
CPP_kAirGasConstant  = 287.1        # kAirGasConstant
CPP_kAbsNull         = -273.15      # kAbsoluteNullCelsius
CPP_kTempGradient    = -6.5 / 1000  # kTempGradient

# ─── Lean model constants (exact rationals, from Atmosphere.lean) ─────────────
LEAN_kR        = Fraction(2871, 10)      # 287.1
LEAN_kAbsNull  = Fraction(-27315, 100)   # -273.15
LEAN_kTempGrad = Fraction(-13, 2000)     # -0.0065


# ─── C++ simulation ──────────────────────────────────────────────────────────

def cpp_density(pressure_pa: float, temperature_celsius: float) -> float:
    """
    Mirrors atmosphere.cpp getDensityFromPressureAndTemp:
        return (pressure_pa / (kAirGasConstant * (temperature_celsius - kAbsoluteNullCelsius)));
    Note: C++ uses float; we use Python double here for simulation. Relative
    error vs true float is < 1e-7.
    """
    T_K = temperature_celsius - CPP_kAbsNull
    return pressure_pa / (CPP_kAirGasConstant * T_K)


def cpp_temp_at_altitude(altitude_m: float) -> float:
    """
    Mirrors atmosphere.cpp getStandardTemperatureAtAltitude:
        return 15.0f + kTempGradient * altitude_m;
    """
    return 15.0 + CPP_kTempGradient * altitude_m


# ─── Lean model simulation (exact rational arithmetic) ───────────────────────

def lean_density(P: Fraction, T_celsius: Fraction) -> Fraction:
    """
    Mirrors Lean: densityRat P T_celsius := P / (kR * (T_celsius - kAbsNull))
    """
    T_K = T_celsius - LEAN_kAbsNull
    return P / (LEAN_kR * T_K)


def lean_temp_at_altitude(h: Fraction) -> Fraction:
    """
    Mirrors Lean: tempAtAltRat h := 15 + kTempGrad * h
    """
    return Fraction(15) + LEAN_kTempGrad * h


# ─── Comparison helper ────────────────────────────────────────────────────────

RTOL = 2e-5   # 20 ppm relative tolerance

def relative_error(a: float, b: float) -> float:
    denom = max(abs(a), abs(b), 1e-30)
    return abs(a - b) / denom


def check(label: str, cpp_result: float, lean_result: float) -> bool:
    rel_err = relative_error(cpp_result, lean_result)
    ok = rel_err <= RTOL
    status = "PASS" if ok else "FAIL"
    sign = "✓" if ok else "✗"
    print(f"  {sign} {status}  {label}")
    print(f"       cpp={cpp_result:.10g}  lean={float(lean_result):.10g}  "
          f"rel_err={rel_err:.2e}")
    return ok


# ─── Main ─────────────────────────────────────────────────────────────────────

def main() -> int:
    with open("test_cases.json") as f:
        cases = json.load(f)

    print("=" * 70)
    print("PX4 Atmosphere Correspondence Test")
    print("C++ float simulation vs Lean 4 rational model")
    print(f"Tolerance: ±{RTOL:.0e} relative")
    print("=" * 70)

    failures = 0

    # ── density tests ────────────────────────────────────────────────────────
    print("\n── getDensityFromPressureAndTemp / densityRat ──")
    for tc in cases["density_cases"]:
        P = tc["pressure_pa"]
        T = tc["temperature_celsius"]
        note = tc["note"]
        T_K = T - CPP_kAbsNull
        if T_K <= 0:
            print(f"  SKIP  P={P}, T={T}°C (T_K ≤ 0, undefined)")
            continue
        cpp_val  = cpp_density(P, T)
        lean_val = lean_density(Fraction(P).limit_denominator(10**12),
                                Fraction(T).limit_denominator(10**12))
        label = f"P={P:9.1f} Pa, T={T:6.1f}°C  ({note})"
        if not check(label, cpp_val, float(lean_val)):
            failures += 1

    # ── temperature tests ─────────────────────────────────────────────────────
    print("\n── getStandardTemperatureAtAltitude / tempAtAltRat ──")
    for tc in cases["temperature_cases"]:
        h = tc["altitude_m"]
        note = tc["note"]
        cpp_val  = cpp_temp_at_altitude(h)
        lean_val = lean_temp_at_altitude(Fraction(h).limit_denominator(10**12))
        label = f"h={h:8.1f} m  ({note})"
        if not check(label, cpp_val, float(lean_val)):
            failures += 1

    # ── invariant spot-checks ─────────────────────────────────────────────────
    print("\n── Invariant checks ──")

    # monotonicity of density in pressure (at ISA SL temperature)
    T_test = 15.0
    P1, P2 = 80000.0, 110000.0
    d1 = cpp_density(P1, T_test)
    d2 = cpp_density(P2, T_test)
    mono_ok = d1 < d2
    print(f"  {'✓ PASS' if mono_ok else '✗ FAIL'}  density_mono_pressure: "
          f"density({P1})={d1:.4f} < density({P2})={d2:.4f}")
    if not mono_ok:
        failures += 1

    # anti-monotonicity of density in temperature (at ISA SL pressure)
    P_test = 101325.0
    T_cold, T_warm = 0.0, 30.0
    d_cold = cpp_density(P_test, T_cold)
    d_warm = cpp_density(P_test, T_warm)
    anti_ok = d_cold > d_warm
    print(f"  {'✓ PASS' if anti_ok else '✗ FAIL'}  density_anti_mono_temp: "
          f"density(T={T_cold})={d_cold:.4f} > density(T={T_warm})={d_warm:.4f}")
    if not anti_ok:
        failures += 1

    # temperature strictly decreasing with altitude
    T_low  = cpp_temp_at_altitude(0.0)
    T_high = cpp_temp_at_altitude(11000.0)
    mono_T_ok = T_low > T_high
    print(f"  {'✓ PASS' if mono_T_ok else '✗ FAIL'}  temp_strictly_decreasing: "
          f"T(0)={T_low} > T(11000)={T_high}")
    if not mono_T_ok:
        failures += 1

    # gas law: density * R * T_K = P
    P_gl = 101325.0
    T_gl = 15.0
    d_gl = cpp_density(P_gl, T_gl)
    T_K_gl = T_gl - CPP_kAbsNull
    reconstruction = d_gl * CPP_kAirGasConstant * T_K_gl
    rel_err_gl = abs(reconstruction - P_gl) / P_gl
    gl_ok = rel_err_gl < 1e-13
    print(f"  {'✓ PASS' if gl_ok else '✗ FAIL'}  gas_law: "
          f"density*R*T_K = {reconstruction:.6f} ≈ P={P_gl}  "
          f"(rel_err={rel_err_gl:.2e})")
    if not gl_ok:
        failures += 1

    # proportionality: density(k*P, T) = k * density(P, T)
    k = 2.0
    P_base = 50000.0
    T_base = 20.0
    d_base  = cpp_density(P_base, T_base)
    d_kbase = cpp_density(k * P_base, T_base)
    prop_err = abs(d_kbase - k * d_base) / max(abs(k * d_base), 1e-30)
    prop_ok = prop_err < 1e-13
    print(f"  {'✓ PASS' if prop_ok else '✗ FAIL'}  proportionality: "
          f"density(2P) = {d_kbase:.6f} ≈ 2*density(P) = {k * d_base:.6f}  "
          f"(rel_err={prop_err:.2e})")
    if not prop_ok:
        failures += 1

    # ── summary ───────────────────────────────────────────────────────────────
    density_n = sum(
        1 for tc in cases["density_cases"]
        if tc["temperature_celsius"] - CPP_kAbsNull > 0
    )
    temp_n = len(cases["temperature_cases"])
    invariant_n = 5
    total = density_n + temp_n + invariant_n

    print()
    print("=" * 70)
    print(f"Results: {total - failures}/{total} passed, {failures} failed")
    if failures == 0:
        print("✓ All correspondence tests PASSED")
        print("  The Lean rational model agrees with the C++ float implementation")
        print(f"  within ±{RTOL:.0e} relative tolerance on all {total} cases.")
    else:
        print(f"✗ {failures} FAILED — correspondence gap found!")
    print("=" * 70)

    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
