# Informal Specification: `math::interpolateN` (Uniform Grid)

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/Functions.hpp` (approx. line 180)
- **Template**: `interpolateN<T, N>(value, y[N])`

---

## Purpose

`interpolateN` maps a scalar `value ∈ [0, 1]` to a piecewise-linear output
defined by `N` equally-spaced nodes `y[0], y[1], …, y[N-1]`. The x-coordinates
of the nodes are implicitly `0, 1/(N-1), 2/(N-1), …, 1`.

Used in PX4 for:
- Motor thrust curves (N=5 or N=9)
- RC stick sensitivity curves
- Control surface deflection mappings

---

## C++ Implementation

```cpp
template<typename T, size_t N>
const T interpolateN(const T &value, const T(&y)[N])
{
    size_t index = constrain((int)(value * (N - 1)), 0, (int)(N - 2));
    return interpolate(value,
                       (T)index / (T)(N - 1),
                       (T)(index + 1) / (T)(N - 1),
                       y[index], y[index + 1]);
}
```

The index selection uses C++ truncation (truncation toward zero for `float`):
`index = floor(value * (N-1))`, clamped to `[0, N-2]`.

---

## Preconditions

- `N ≥ 2` (must have at least two nodes)
- `value` is a finite floating-point value (NaN/inf behaviour is unspecified)
- The y array has exactly `N` elements

---

## Postconditions

1. **Node exactness**: `interpolateN(k/(N-1), y) = y[k]` for `k = 0, 1, …, N-1`.
2. **Range containment**: if `y[0] ≤ y[1] ≤ … ≤ y[N-1]` and `0 ≤ value ≤ 1`,
   then `y[0] ≤ result ≤ y[N-1]`.
3. **Clamped outside range**: for `value < 0`, result = `y[0]`; for `value > 1`,
   result = `y[N-1]`.
4. **Piecewise linearity**: within each segment `[k/(N-1), (k+1)/(N-1)]`, the
   output is linear in `value`.
5. **Continuity**: output is continuous at every breakpoint `k/(N-1)`.
6. **Monotonicity**: if `y` is non-decreasing and `v1 ≤ v2`, then
   `interpolateN(v1, y) ≤ interpolateN(v2, y)` (within each segment).
7. **Constancy**: if all `y[i] = c`, then `interpolateN(value, y) = c`.

---

## Invariants

- Output is a **convex combination** of adjacent y-values within each segment.
- The segment index computation is safe: `constrain(...)` guarantees
  `0 ≤ index ≤ N-2`, so y[index] and y[index+1] are always valid accesses.

---

## Edge Cases

| Scenario | Expected behaviour |
|----------|--------------------|
| `value = 0` | Returns `y[0]` exactly |
| `value = 1` | Returns `y[N-1]` exactly |
| `value = k/(N-1)` | Returns `y[k]` exactly |
| `value < 0` | Returns `y[0]` (clamped by `interpolate`) |
| `value > 1` | Returns `y[N-1]` (clamped by `interpolate`) |
| `N = 2` | Reduces to `interpolate(value, 0, 1, y[0], y[1])` |
| All y equal | Returns the constant value |
| `value` = NaN | Unspecified (not in C++ spec; float) |

---

## Inferred Intent

`interpolateN` is a generalisation of `interpolate` to N equally-spaced points.
The key design decisions are:
1. **Uniform x-spacing**: simplifies the index computation to a scalar multiply +
   truncate, avoiding storage of x-coordinates.
2. **Clamping at endpoints**: values outside `[0, 1]` are handled by `interpolate`'s
   clamping, which returns the nearest endpoint value.
3. **Exact at nodes**: the `interpolate` call uses the segment endpoints exactly,
   so `interpolateN(k/(N-1), y) = y[k]` without rounding error (in exact arithmetic).

---

## Open Questions

- **Float truncation vs floor**: C++ `(int)(float)` truncates toward zero (same as
  floor for positive floats). For negative `value`, truncation and floor differ. Is
  negative `value` supported? The clamping in `constrain` handles index < 0, so the
  output would be `y[0]` regardless — but the intermediate `(int)(float)` cast could
  overflow for very negative values.
- **Monotonicity across segments**: the spec only guarantees monotonicity within a
  segment when using strict interior conditions. Global monotonicity (across the
  entire `[0, 1]` range) follows from the combination of segment monotonicity and
  the node exactness property, but requires a per-node case split.

---

## Examples

For `N=3`, `y = {0, 0.25, 1}` (convex motor curve):
- `value = 0` → `0`
- `value = 0.25` → `0.125` (halfway through segment 0)
- `value = 0.5` → `0.25` (at node 1)
- `value = 0.75` → `0.625` (halfway through segment 1)
- `value = 1` → `1`
