# Informal Specification: PX4 PID Controller

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/pid/PID.cpp`, `src/lib/pid/PID.hpp`

---

## Purpose

The PX4 `PID` class implements a generic proportional–integral–derivative (PID)
controller used throughout the flight controller (attitude, rate, position, etc.).
It computes a bounded control output from a setpoint and current feedback value,
with integral wind-up limiting and derivative filtering.

---

## Simplified C++ (relevant methods)

```cpp
float PID::update(const float feedback, const float dt, const bool update_integral)
{
    const float error = _setpoint - feedback;
    const float output = (_gain_proportional * error) + _integral
                       + (_gain_derivative * updateDerivative(feedback, dt));
    if (update_integral) updateIntegral(error, dt);
    _last_feedback = feedback;
    return math::constrain(output, -_limit_output, _limit_output);
}

void PID::updateIntegral(float error, const float dt)
{
    const float integral_new = _integral + _gain_integral * error * dt;
    if (std::isfinite(integral_new))
        _integral = math::constrain(integral_new, -_limit_integral, _limit_integral);
}

float PID::updateDerivative(float feedback, const float dt)
{
    float feedback_change = 0.f;
    if ((dt > FLT_EPSILON) && std::isfinite(_last_feedback))
        feedback_change = (feedback - _last_feedback) / dt;
    return feedback_change;
}
```

---

## Preconditions

- `dt > 0` (time step) — derivative is only computed when `dt > FLT_EPSILON`.
- `_limit_output ≥ 0` — symmetric output clamp bound.
- `_limit_integral ≥ 0` — symmetric integral clamp bound.
- `_gain_proportional`, `_gain_integral`, `_gain_derivative` are finite real numbers.

---

## Postconditions

### Output clamping
The return value of `update` always satisfies:
```
-_limit_output ≤ output ≤ _limit_output
```

### Integral clamping
After any call to `updateIntegral`, the integral accumulator satisfies:
```
-_limit_integral ≤ _integral ≤ _limit_integral
```

### Equilibrium (steady-state zero)
If `_setpoint = feedback`, `_integral = 0`, and `_last_feedback = feedback`
(i.e., the controller has been at this point for at least one prior step), then
`update` returns `0`.

### First-call equilibrium
If `_setpoint = feedback` and `_integral = 0` and this is the first call
(`_last_feedback` is unset / NaN), then `update` returns `0`.

### Derivative on first call
`updateDerivative` returns `0` on the first call (when `_last_feedback` is NaN).

### Derivative at steady state
If `dt > 0` and `_last_feedback = feedback` (no change), then
`updateDerivative` returns `0`.

### Zero-error integral evolution
If `error = 0` at every step, then `_integral` remains unchanged.

### Integral range preservation under iteration
No matter how many steps are taken, `_integral` stays in
`[-_limit_integral, _limit_integral]` as long as that bound starts satisfied.

### Monotonicity in setpoint
For fixed feedback, dt, gains, limits, and state:
`_setpoint ≤ _setpoint'` implies `output ≤ output'`.

### Monotonicity in integral state
For fixed arguments, a larger integral accumulator leads to a larger or equal output.

---

## Invariants

1. **Output bounded**: `|output| ≤ _limit_output` at all times.
2. **Integral bounded**: `|_integral| ≤ _limit_integral` at all times.
3. **Error-driven output**: output is a linear combination of proportional error,
   accumulated integral, and derivative term — clamped at the limits.

---

## Edge Cases

- **First call** (`_last_feedback = NaN`): derivative term is 0; output depends only
  on proportional and integral terms.
- **Zero dt** or **negative dt**: derivative is 0 (matches `dt ≤ 0` guard).
- **Perfect tracking** (`setpoint = feedback`, `integral = 0`): output is exactly 0.
- **Integral saturation**: once `_integral` hits `±_limit_integral`, further same-sign
  errors do not increase magnitude beyond the limit.
- **Non-update call** (`update_integral = false`): integral is unchanged; output is
  computed from current integral state without updating it.

---

## Multi-step Convergence

When `feedback = _setpoint` for every step (zero error):
- The integral term does not change.
- The derivative term is 0 after the first step.
- The output is 0 at every step after the first.

This captures the notion that a well-configured PID controller "settles" at the
setpoint with no residual demand.

---

## Approximations / Out of Scope

- **Floating-point rounding**: the formal model uses `Int` (or `Rat`) to obtain exact
  proofs. Floating-point truncation and rounding are not modelled.
- **NaN / infinity handling**: `isfinite` guards are modelled as the first-call
  abstraction (`Option Int`) only; general NaN propagation is out of scope.
- **`FLT_EPSILON` guard**: modelled as `dt > 0` (integer comparison).
- **Gains and limits as integers**: the model uses integer arithmetic, abstracting
  the gains. The real implementation uses 32-bit floats.
- **`update_integral` flag**: the integral update is always applied in the model;
  the flag is abstracted as a separate function call.

---

## Examples

| setpoint | feedback | dt | gainP | gainD | limitO | integral (in) | last_fb | expected output |
|----------|----------|----|-------|-------|--------|--------------|---------|-----------------|
| 10       | 0        | 1  | 1     | 0     | 100    | 0            | none    | 10              |
| 0        | 0        | 1  | 1     | 0     | 100    | 0            | none    | 0               |
| 0        | 0        | 1  | 1     | 0     | 100    | 0            | some 0  | 0               |
| 5        | 5        | 1  | 2     | 3     | 100    | 0            | some 5  | 0               |
| 10       | 0        | 1  | 1     | 0     | 5      | 0            | none    | 5 (clamped)     |

---

## Open Questions

1. **Gain sign conventions**: is negative `gainP` expected / safe?  The model does
   not restrict gain signs.  A negative proportional gain would produce
   a negative output for positive error, which could be intentional (e.g., pitch
   attitude where sign convention is reversed).

2. **Integral reset**: should the integral be reset when `_setpoint` changes
   significantly?  This is common in PID implementations to prevent wind-up.
   Not modelled here.

3. **Derivative on setpoint vs. feedback**: some PID implementations apply the
   derivative to the setpoint error, not just feedback.  PX4 applies it to
   feedback change only (derivative kick prevention).  Is this always intentional?
