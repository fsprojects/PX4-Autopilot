# LowPassFilter2p Correspondence Tests

🔬 *Lean Squad — Route B correspondence validation.*

## Purpose

Verifies that the Lean 4 model in `formal-verification/lean/FVSquad/LowPassFilter2p.lean`
exactly matches the C++ implementation in
`src/lib/mathlib/math/filter/LowPassFilter2p.hpp` on a representative set of test cases.

## What is compared

Both the Lean model and the C++ implementation implement a **Direct Form II second-order IIR filter**:

```
w0  = sample - d1*a1 - d2*a2
out = w0*b0 + d1*b1 + d2*b2
new_d1 = w0,  new_d2 = d1
```

The test harness implements both as pure Python using `fractions.Fraction` (exact rational
arithmetic), eliminating any floating-point discrepancy and isolating the algorithmic
correspondence.

## Running

```bash
python3 test_correspondence.py
```

Expected output:
```
OK: 28/28 test cases passed
```

## Test coverage

| Category | Cases | Description |
|----------|-------|-------------|
| Disabled pass-through | 5 | `b0=1, b1=b2=a1=a2=0` — output = input |
| Butterworth-like rational | 7 | `b1=2*b0, b2=b0`, unit step, neg step, alternating, nonzero init, large, fractional |
| Coefficient set B | 5 | Independent rational coefficients, impulse, ramp, decay |
| DC-unity | 4 | `b0+b1+b2 = 1+a1+a2`, constant input (DC steady-state) |
| Zero-input decay | 2 | Nonzero initial state, zero input, exponential decay |
| Single-sample | 5 | Boundary: single application |
| **Total** | **28** | — |

## Correspondence status

- **Lean model**: `lpf2pApply` in `LowPassFilter2p.lean` — exact algorithmic match ✅
- **C++ source**: `LowPassFilter2p<T>::apply` in `src/lib/mathlib/math/filter/LowPassFilter2p.hpp`
- **Correspondence level**: **exact** (same arithmetic operations, same state update order)
- **Abstracted**: IEEE 754 float arithmetic, `set_cutoff_frequency` (uses `tanf`, `cosf`), NaN/Inf handling

## Known limitations

- Tests use exact rational arithmetic. Float-specific rounding errors are not covered.
- `set_cutoff_frequency` (Butterworth coefficient computation) is not modelled in Lean.
- The `disable()` branch (invalid parameters) is covered via the disabled-coefficients cases.
