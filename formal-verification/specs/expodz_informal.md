# Informal Specification: `expo_deadzone` (Expo + Deadzone Composition)

🔬 *Lean Squad automated formal verification.*

**Target**: `expo(deadzone(value, dz), e)` composition  
**C++ source**: `src/lib/mathlib/math/Functions.hpp`  
**Lean file**: `formal-verification/lean/FVSquad/ExpoDeadzone.lean`

---

## Purpose

The `expo_deadzone` pipeline is the primary RC (radio-control) stick input processor
used throughout PX4. Raw stick input (a float in `[-1, 1]`) is first passed through a
**deadzone** to suppress stick drift near the centre, then through an **exponential
curve** to adjust sensitivity: gentle near centre, full-authority at the extremes.

In C++ this is expressed as the composition:

```cpp
float expo_deadzone(float value, float e, float dz) {
    return expo(deadzone(value, dz), e);
}
```

Both `expo` and `deadzone` are individually documented in their own informal specs.
This document specifies the *composed* behaviour.

---

## Inputs

| Parameter | Type  | Valid range      | Meaning                                           |
|-----------|-------|------------------|---------------------------------------------------|
| `value`   | float | `[-1, 1]`        | Raw stick input; values outside clipped by caller |
| `e`       | float | `[0, 1]`         | Expo factor: 0 = linear, 1 = full cubic curve     |
| `dz`      | float | `[0, 1)`         | Deadzone width; inputs with `|value| ≤ dz` → 0   |

---

## Preconditions

- `value` is a finite float; NaN / ±∞ not expected in normal operation.
- `0 ≤ e ≤ 1`: expo factor is in unit interval.
- `0 ≤ dz < 1`: deadzone width is valid (strictly less than 1 to avoid dividing by zero in deadzone normalisation).

---

## Postconditions

1. **Range**: output is always in `[-1, 1]` for any valid inputs.
2. **Zero inside deadzone**: if `|value| ≤ dz`, then `expo_deadzone(value, e, dz) = 0`.
3. **Full deflection**: `expo_deadzone(1, e, dz) = 1` and `expo_deadzone(-1, e, dz) = -1` for valid `e` and `dz`.
4. **Odd symmetry**: `expo_deadzone(-value, e, dz) = -expo_deadzone(value, e, dz)` (point-symmetric about the origin).
5. **Zero input → zero output**: `expo_deadzone(0, e, dz) = 0`.
6. **Monotone in value**: if `v₁ ≤ v₂` then `expo_deadzone(v₁, e, dz) ≤ expo_deadzone(v₂, e, dz)`.
7. **e = 0 (linear)**: `expo_deadzone(value, 0, dz) = deadzone(value, dz)` — pure deadzone, no curve.
8. **e = 1 (cubic)**: `expo_deadzone(value, 1, dz) = deadzone(value, dz)³`.
9. **dz = 0 (no deadzone)**: `expo_deadzone(value, e, 0) = expo(value, e)`.

---

## Invariants

- The output sign always matches the sign of the input (when input is outside the deadzone).
- The output is strictly 0 for inputs strictly inside the deadzone (`|value| < dz`).
- The mapping is continuous at the deadzone edge (no jump discontinuity — the deadzone normalises output to start from 0 at the boundary).

---

## Edge Cases

| Scenario | Expected output |
|----------|----------------|
| `value = 0` | `0` |
| `|value| ≤ dz` | `0` |
| `value = 1, e = 0, dz = 0` | `1` |
| `value = 1, e = 1, dz = 0` | `1` (cube of 1 is 1) |
| `value = -1, e = 0.5, dz = 0.1` | `-1` (full deflection) |
| `dz = 0, e = 0` | `value` (identity) |

---

## Composition Structure

The composed function factors cleanly through two independently specified functions:

```
value ──▶ deadzone(·, dz) ──▶ expo(·, e) ──▶ output
```

Properties of the composition follow from the properties of each component:
- `deadzone` maps to `[-1, 1]`, is odd-symmetric, monotone, and zero in the deadzone.
- `expo` maps `[-1, 1]` to `[-1, 1]`, is odd-symmetric, monotone, and fixes ±1.

By function composition, all of these properties are inherited by `expo_deadzone`.

---

## Inferred Intent

The design intention is to create a smooth, customisable stick input response that:
1. Ignores small unintentional inputs near zero (deadzone).
2. Provides linear-to-cubic interpolation of sensitivity (expo).
3. Never saturates or inverts: full stick always produces full authority.
4. Is symmetric: the left and right, up and down responses are mirror images.

The RC pilot can independently tune the deadzone (to match their physical controller's slop) and the expo factor (to set how aggressive the curve is).

---

## Open Questions

1. **Deadzone normalisation**: does the C++ `deadzone` function normalise the output to `[0, 1]` at the boundary (remapping `[dz, 1]` to `[0, 1]`) or just subtract `dz`? This affects whether the full-deflection postcondition holds exactly. *(Current understanding: normalisation is applied — see `deadzone_informal.md`.)*
2. **Float clamping**: the input `value` is documented as `[-1, 1]` but is not explicitly clamped before the deadzone call. Is it guaranteed by callers? Could a value of `1.001` (from floating-point accumulation) ever appear?
3. **Thread safety**: the functions are pure (no state), so composition is trivially thread-safe, but this assumption should be verified at call sites.

---

## Examples

Using exact rational arithmetic (`Rat`):

| value | e    | dz  | deadzone output | expo output |
|-------|------|-----|-----------------|-------------|
| 0     | 0.5  | 0.1 | 0               | 0           |
| 0.1   | 0.5  | 0.1 | 0               | 0           |
| 0.5   | 0    | 0.2 | 0.375           | 0.375       |
| 0.5   | 1    | 0   | 0.5             | 0.125       |
| 1     | 0.5  | 0.2 | 1               | 1           |
| -0.5  | 0.5  | 0   | -0.5            | −(expo(0.5,0.5)) |

---

*Generated by Lean Squad run 120.*
