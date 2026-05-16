# BlockIntegralTrap — Informal Specification

🔬 *Lean Squad automated formal verification*

## Purpose

`BlockIntegralTrap` implements a **trapezoidal-rule integrator with symmetric
saturation** from PX4-Autopilot's `controllib`. It accumulates an integral of a
floating-point signal using the trapezoidal rule and clamps the accumulated
value symmetrically to `[-max, max]` on every step.

**C++ sources**:
- `src/lib/controllib/BlockIntegralTrap.hpp` (declaration, lines 72–100)
- `src/lib/controllib/BlockIntegralTrap.cpp` (definition, lines 47–53)

```cpp
float BlockIntegralTrap::update(float input)
{
    // trapezoidal integration
    setY(_limit.update(getY() +
              (getU() + input) / 2.0f * getDt()));
    setU(input);
    return getY();
}
```

`_limit` is a `BlockLimitSym` instance that clamps its argument to `[-max, max]`.

---

## State

| Field | Type | Meaning |
|-------|------|---------|
| `_y`  | `float` | Current integrator output (the accumulated integral) |
| `_u`  | `float` | Previous input sample (used for the trapezoidal midpoint) |

**Parameters** (set at construction or via block parameters):
| Parameter | Meaning |
|-----------|---------|
| `getDt()` | Timestep `dt > 0` (seconds) |
| `getMax()` | Saturation bound `max ≥ 0`; output is clamped to `[-max, max]` |

---

## Preconditions

1. `dt ≥ 0` — a non-negative timestep.
2. `max ≥ 0` — a non-negative saturation bound.
3. Both `input` and the current state `_y`, `_u` are finite (no NaN or ±∞).

---

## Postconditions

After `update(input)`:

1. **Output is in range**: `_y ∈ [-max, max]`.
2. **Trapezoidal increment**: if the unsaturated value `_y + (u_prev + input)/2 * dt`
   is within `[-max, max]`, then `_y` equals that unsaturated value exactly.
3. **Previous input stored**: `_u` is set to `input`.
4. **Zero input / zero state**: if `input = 0` and `_u = 0` and `_y = 0` then
   `_y` remains 0.
5. **Positive inputs accumulate**: if `input ≥ 0` and `_u ≥ 0` and `dt > 0`
   and `_y < max`, then the new `_y ≥` old `_y` (the integral grows).
6. **Negative inputs drain**: symmetric to the positive case.
7. **Saturation stickiness (positive)**: if `_y = max` and `input ≥ 0` and `_u ≥ 0`
   and `dt ≥ 0`, the new `_y = max` (remains saturated).
8. **Saturation stickiness (negative)**: symmetric.

---

## Invariants

- The output `_y` always satisfies `|_y| ≤ max` (bounded by the saturation limit).
- This invariant is maintained for **all** inputs and is re-established on every
  call even if `_y` was previously set to an out-of-range value.

---

## Edge Cases

| Case | Expected Behaviour |
|------|--------------------|
| `dt = 0` | Trapezoidal increment is 0; `_y` unchanged (clamped to itself) |
| `input = 0, _u = 0` | No change to `_y` if `dt = 0`; otherwise unchanged if already at 0 |
| `max = 0` | Output is always 0 regardless of input |
| Very large input | `_y` saturates to `max` (or `-max`) and stays there |
| Alternating `+M / -M` input | Trapezoidal midpoint is 0 every step; `_y` stays at its current value |
| First call (`_u = 0` by default) | The first increment is `input/2 * dt` (trapezoidal with 0 as prev sample) |

---

## Examples

All examples use `dt = 1`, `max = 10`:

| `_y` (before) | `_u` (before) | `input` | `_y` (after) | `_u` (after) |
|---------------|---------------|---------|--------------|--------------|
| 0             | 0             | 2       | 1.0          | 2            |
| 1             | 2             | 4       | 4.0          | 4            |
| 9             | 4             | 10      | 10.0 (sat)   | 10           |
| 0             | 0             | -4      | -2.0         | -4           |
| -9            | -4            | -10     | -10.0 (sat)  | -10          |
| 5             | 4             | -4      | 5.0          | -4           |

*(In the last row: `5 + (4 + -4)/2 * 1 = 5`; the positive and negative inputs cancel.)*

---

## Inferred Intent

- The trapezoidal rule (rather than Euler forward/backward) is chosen to reduce
  integration error by averaging the previous and current input.
- The symmetric saturation `_limit` prevents integrator wind-up — a common
  failure mode in feedback controllers.
- Setting `_u = input` at the end ensures the next call uses the current
  input as the "previous" value, maintaining the trapezoidal averaging.

---

## Open Questions

1. **Initial `_u`**: Is `_u` always 0 at construction? The header shows
   `float _u{0}`, so yes — but this means the first call uses `(0 + input)/2 * dt`
   as the increment. Is this the intended behaviour, or should the first call be
   skipped (as in `FilteredDerivative`)?
2. **Thread safety**: The class uses non-atomic reads/writes of `_y` and `_u`.
   Is `update` always called from a single thread?
3. **dt sign**: The C++ code does not guard against negative `dt`. Should the
   Lean spec assume `dt ≥ 0` or `dt > 0`?

---

## Mapping to Lean 4 Model

`formal-verification/lean/FVSquad/BlockIntegralTrap.lean` models this with:

- `ITParams`: `{ dt : Rat, limit : Rat }` (parameters)
- `ITState`: `{ y : Rat, u : Rat }` (state)
- `itUpdate p s input`: one-step update returning the new `ITState`
- `itFold p s₀ inputs`: fold `itUpdate` over a list of inputs

Key properties proved in the Lean file:
- `itUpdate_y_bounded`: output always in `[-limit, limit]`
- `itUpdate_u_eq_input`: `_u` is set to `input` after each call
- `itUpdate_y_exact`: if the raw increment is in range, output equals the exact value
- `itFold_y_in_range`: saturation invariant maintained over all steps
- `itUpdate_trap_mono_input`: monotone in input (larger input → larger output)
- `itUpdate_saturated_pos/neg`: saturation is sticky
