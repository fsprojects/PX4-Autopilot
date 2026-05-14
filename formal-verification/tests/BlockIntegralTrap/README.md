# BlockIntegralTrap — Correspondence Tests

🔬 *Lean Squad — Route B executable correspondence validation.*

## Purpose

Validates that the Lean 4 implementation model in
[`formal-verification/lean/FVSquad/BlockIntegralTrap.lean`](../../lean/FVSquad/BlockIntegralTrap.lean)
matches the C++ source in
[`src/lib/controllib/BlockIntegralTrap.cpp`](../../../src/lib/controllib/BlockIntegralTrap.cpp)
on a shared set of test cases.

## Method

Both models are executed in Python:

- **Lean model** — faithfully re-implemented using Python `fractions.Fraction`
  (exact rational arithmetic), mirroring `itUpdate` and `itFold` from the Lean file.
- **C++ model** — faithfully re-implemented using Python `float`, mirroring the C++
  trapezoidal update loop exactly.

Results are compared with a small floating-point tolerance (≤ 1e-6 relative) to
account for IEEE 754 rounding that the rational Lean model does not capture.

## How to Run

```bash
cd formal-verification/tests/BlockIntegralTrap
python3 test_correspondence.py
```

Expected output:
```
BlockIntegralTrap correspondence tests: 120/120 passed
All tests PASSED — Lean model matches C++ algorithm on all cases.
```

## Test Cases

The harness covers 20 named scenarios plus 100 random property-based cases:

| Scenario | Description |
|----------|-------------|
| `zero_state_zero_input` | Integrator stays at zero with all-zero inputs |
| `constant_positive_input` | Monotone accumulation |
| `constant_negative_input` | Monotone negative accumulation |
| `saturation_positive` | Large positive input saturates output at +limit |
| `saturation_negative` | Large negative input saturates at −limit |
| `saturation_already_at_limit` | Starts at limit, remains clamped |
| `saturation_already_neg_limit` | Starts at −limit, remains clamped |
| `step_up_then_step_down` | Step-up followed by step-down |
| `alternating_sign` | Alternating ±1 inputs (net zero) |
| `large_dt_hits_limit_fast` | Big dt causes rapid saturation |
| `ramp_input` | Linearly increasing input sequence |
| `nonzero_initial_state` | Non-zero initial y and u |
| `previous_input_remembered` | Trapezoidal rule uses previous input |
| `limit_boundary_single_step` | Single step lands exactly at limit |
| `dt_half` | Half-second timestep |
| `two_updates_trapezoid` | Two-step trapezoidal check |
| `three_updates` | Three-step sequence |
| `zero_dt_no_integration` | dt=0: output unchanged regardless of input |
| `tiny_inputs` | Accumulation of very small inputs (fractional) |
| `fractional_limit` | Rational limit (3/2) |
| `bounded_property` (×100) | Random inputs: output always in [−limit, limit] |

## Coverage and Limitations

**Covered:**
- Correct trapezoidal formula `y' = clamp(y + (u_prev + u) / 2 * dt, −lim, lim)`
- Correct update of `u_prev` to `input` after each step
- Saturation clamping in both directions
- Multi-step sequences (itFold correspondence)
- The `itUpdate_y_bounded` invariant (random testing)

**Not covered:**
- IEEE 754 floating-point rounding (the Lean model uses exact rationals)
- NaN / infinity / denormal inputs (C++ behaviour undefined here)
- Concurrent or re-entrant calls

## Last Run

- **Date**: 2026-05-14
- **Result**: 120/120 passed
- **Python version**: 3.x (`python3 test_correspondence.py`)
