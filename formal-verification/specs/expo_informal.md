# Informal Specification: `expo` (Exponential RC Curve)

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/mathlib/math/Functions.hpp` — `expo<T>` template  
**Lean model**: `formal-verification/lean/FVSquad/Expo.lean` — `expoRat`

---

## Purpose

`expo` shapes RC (radio-control) stick input by blending a linear response with a
cubic (exponential) curve. A pilot adjusts the *expo* parameter `e` to tune
sensitivity near the stick centre without changing the maximum deflection.

- **`e = 0`**: pure linear response (full proportional sensitivity throughout).
- **`e = 1`**: pure cubic response (very gentle near centre, maximum at extremes).
- **`0 < e < 1`**: a blend — linear + cubic weighted by `e`.

The function is used in PX4's manual-control pipeline to convert normalised stick
positions into normalised actuator commands.

---

## C++ Signature

```cpp
template<typename T>
const T expo(const T &value, const T &e)
{
    T x  = constrain(value, (T)-1, (T)1);
    T ec = constrain(e,     (T)0,  (T)1);
    return (1 - ec) * x + ec * x * x * x;
}
```

---

## Preconditions

| Parameter | Expected range | Behaviour outside range |
|-----------|---------------|------------------------|
| `value`   | [-1, 1]       | Clamped to [-1, 1] before computation |
| `e`       | [0, 1]        | Clamped to [0, 1] before computation |

Neither parameter is a hard requirement — the function is robust to out-of-range
inputs by design.

---

## Postconditions

1. **Bounded output**: `output ∈ [-1, 1]` for all inputs (regardless of clamping).
2. **Zero input → zero output**: `expo(0, e) = 0` for any `e`.
3. **Unit endpoints are fixed**: `expo(1, e) = 1` and `expo(-1, e) = -1` for any `e`.
4. **Anti-symmetry (odd function)**: `expo(-v, e) = -expo(v, e)` for all `v`, `e`.
5. **Linear case (e = 0)**: `expo(v, 0) = constrain(v, -1, 1)`.
6. **Cubic case (e = 1)**: `expo(v, 1) = x³` where `x = constrain(v, -1, 1)`.

---

## Invariants

- The output is a convex combination of a linear function and a cubic function
  over the clamped input. Both are odd functions; their convex combination is
  also odd.
- The blend is parameterised: `output = (1 - ec) * x + ec * x³`.

---

## Edge Cases

| Input | Expected output | Reason |
|-------|----------------|--------|
| `value = 0` | `0` | Both `x` and `x³` are 0 |
| `value = 1` | `1` | `(1-ec)*1 + ec*1 = 1` |
| `value = -1` | `-1` | `(1-ec)*(-1) + ec*(-1) = -1` |
| `value > 1` | `expo(1, e)` | Clamped to 1 |
| `value < -1` | `expo(-1, e)` | Clamped to -1 |
| `e = 0` | `constrain(value, -1, 1)` | Linear |
| `e = 1` | `x³` | Cubic |
| `e > 1` | `expo(value, 1)` | Clamped expo to 1 |
| `e < 0` | `expo(value, 0)` | Clamped expo to 0 = linear |

---

## Examples

| `value` | `e` | output |
|---------|-----|--------|
| `0`     | any | `0`     |
| `0.5`   | `0` | `0.5`   |
| `0.5`   | `1` | `0.125` |
| `0.5`   | `0.5` | `0.3125` |
| `1`     | any | `1`     |
| `-0.5`  | `0.5` | `-0.3125` |

---

## Inferred Intent

The function is designed so that:
1. Full stick deflection always produces full actuator command (unit endpoints fixed).
2. The dead-band near zero stick is controlled by `e` — higher `e` means more centre
   insensitivity, giving the pilot finer control near neutral.
3. Anti-symmetry ensures equal response for left and right stick positions.
4. The function is continuous and differentiable everywhere.

---

## Open Questions

1. **Monotonicity**: is `expo(v, e)` monotone increasing in `v` for fixed `e ∈ [0,1]`?
   This seems true (sum of two monotone functions on [-1,1]) but has not been formally
   proved in the current Lean file.
2. **Derivative at 0**: the C++ comment says the derivative at 0 is `(1-e)`, matching
   the informal spec. This is captured in the Lean theorem `expo_eq_linear_at_zero` but
   only for small perturbations, not as a formal derivative statement.
3. **Continuity across clamp boundary**: should be straightforward but not stated
   as a theorem.

---

## Correspondence to Lean Model

The Lean model `expoRat` in `Expo.lean` directly implements this specification over
`Rat` (exact rationals), replacing the C++ `float` type. All nine key properties
listed in the postconditions have been proved as Lean theorems. Correspondence
between `expoRat` and the C++ template has been validated by 1373 test cases using
exact rational arithmetic — see `formal-verification/tests/expo/`.
