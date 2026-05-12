# Informal Specification: `BlockHighPass::update`

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/controllib/BlockHighPass.hpp`, `src/lib/controllib/BlockHighPass.cpp`

## Purpose

`BlockHighPass` implements a first-order IIR (Infinite Impulse Response) high-pass filter.
It passes rapidly-changing signal components (high frequencies) while attenuating slowly-changing
components (low frequencies) including DC (constant signals). Used in PX4 for vibration detection,
gyroscope bias filtering, and angular rate processing.

## State

```
_u : float   -- previous input sample
_y : float   -- previous output sample
fCut : float -- cut-off frequency in Hz
dt   : float -- sample period in seconds (from Block superclass)
```

## Algorithm

```cpp
float BlockHighPass::update(float input) {
    float b = 2 * M_PI_F * getFCut() * getDt();
    float a = 1 / (1 + b);
    setY(a * (getY() + input - getU()));
    setU(input);
    return getY();
}
```

The recurrence in closed form:
```
y_k = a * (y_{k-1} + u_k - u_{k-1})
```
where `a = 1 / (1 + b)`, `b = 2π * fCut * dt`.

## Preconditions

- `fCut > 0` and `dt > 0` (positive cut-off frequency and sample period)
- Equivalent: `b > 0` and hence `0 < a < 1`
- Input is a finite, non-NaN float (rational model: any Rat)

## Postconditions

After one call to `update(input)`:
- `_u = input` (current input stored as previous)
- `_y = a * (prev_y + input - prev_u)`
- Return value = new `_y`

## Key Properties

### Coefficient bounds
When `b > 0` (i.e., `fCut > 0` and `dt > 0`):
- `0 < a < 1`
- Specifically: `a = 1 / (1 + b) ∈ (0, 1)`

### DC Blocking (constant input)
When the input is constant (`u_k = u` for all k):
- Each step: `y_k = a * y_{k-1}` (reduces to pure scalar decay)
- After n steps: `y_n = a^n * y_0`
- Since `0 < a < 1`, `a^n → 0` as `n → ∞`
- **The filter blocks DC**: a constant input drives the output to zero

### Stability
- If `y_0 ≥ 0` and `a ≥ 0`, then `y_n ≥ 0` for all n (non-negativity preserved)
- If `y_0 > 0` and `0 < a < 1`, then `{y_n}` is strictly decreasing
- Output is bounded: `|y_n| ≤ |y_0|` for `0 < a ≤ 1`

### Step response
On a step input (signal changes from 0 to 1 at k=0):
- First step: `y_1 = a * (0 + 1 - 0) = a`
- Subsequent steps (constant input = 1): `y_k = a^(k-1) * a = a^k`
- Converges to 0 (DC blocked)

## Edge Cases

- **Zero cut-off frequency** (`fCut = 0`): `b = 0`, `a = 1`, filter becomes identity (`y_k = y_{k-1} + u_k - u_{k-1}`), i.e., pure differentiator (not a valid HPF)
- **First call** (initial state `_u = 0`, `_y = 0`): `y_1 = a * (0 + input - 0) = a * input`
- **Large dt**: Large `b` → very small `a` → aggressive high-pass (attenuates more)

## Approximations in Lean Model

- `Rat` model: exact rational arithmetic (no float rounding, NaN, or overflow)
- Abstract `a` parameter: the closed-form `a = 1/(1+b)` is used but `b` is left abstract; `a` is treated as satisfying `0 < a < 1`
- Steady-state focus: theorems concern the constant-input trajectory
- Initial transient: not modelled (theorems assume constant input from step 0)

## Open Questions

1. What is the precise float rounding error in `a = 1 / (1 + b)` for typical `fCut/dt` values?
2. What happens at the exact cutoff frequency (sinusoidal input at `fCut` Hz)? The gain should be `1/√2 ≈ 0.707`.
3. Is there any overflow risk for `b = 2π * fCut * dt` at extreme parameter values?
