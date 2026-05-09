# Informal Specification: `math::negate<int16_t>`

🔬 Lean Squad automated formal verification.

## Source

- **File**: `src/lib/mathlib/math/Functions.hpp`, lines 257–270
- **Lean model**: `formal-verification/lean/FVSquad/Negate16.lean`

---

## Purpose

PX4's `math::negate<int16_t>` computes the negation of an `int16_t` value while
avoiding two C++ undefined-behaviour (UB) hazards:

1. **Negating `INT16_MIN` overflows**: In C++, `-INT16_MIN` is UB for signed integers
   because `−(−32768) = 32768` does not fit in `int16_t`. The specialisation handles
   this by mapping `INT16_MIN → INT16_MAX` (a common convention).
2. **Symmetry hack**: To make the function a bijection on the `int16_t` domain, the
   implementation also maps `INT16_MAX → INT16_MIN`. However, as shown by formal
   verification below, this choice makes the function neither injective nor
   involutive (self-inverse) everywhere.

---

## C++ Source

```cpp
template<>
constexpr int16_t negate<int16_t>(int16_t value)
{
    if (value == INT16_MAX) {
        return INT16_MIN;

    } else if (value == INT16_MIN) {
        return INT16_MAX;
    }

    return -value;
}
```

---

## Preconditions

- Input `value` is any `int16_t`, i.e., `value ∈ [−32768, 32767]`.

---

## Postconditions

| Input range | Output |
|---|---|
| `value == INT16_MAX` (32767) | `INT16_MIN` (−32768) |
| `value == INT16_MIN` (−32768) | `INT16_MAX` (32767) |
| All other values | `−value` (mathematical negation) |

---

## Invariants

- **Range preserved**: output is always in `[INT16_MIN, INT16_MAX]` — no overflow possible.

---

## Edge Cases and Formal Findings

The two boundary cases interact in subtle ways discovered by FV:

### Finding 1: Not Involutive at `x = −32767`

`negate(negate(−32767)) = negate(32767) = −32768 ≠ −32767`

The function is self-inverse everywhere in `[INT16_MIN, INT16_MAX]` **except** for
`x = −32767 = −INT16_MAX`. This is the only exception.

### Finding 2: Not Injective

`negate(−32767) = 32767` and `negate(−32768) = 32767`, yet `−32767 ≠ −32768`.

Two distinct inputs produce the same output (`32767`), so `negate` is **not injective**.

### Finding 3: Not Surjective (Image Gap)

`−32767` has no preimage under `negate`:

- For `x = INT16_MAX`: `negate(32767) = −32768`
- For `x = INT16_MIN`: `negate(−32768) = 32767`
- For all other `x`: `negate(x) = −x`; `−x = −32767` iff `x = 32767 = INT16_MAX`,
  but then `negate(32767) = −32768`, not `−32767`.

So `−32767` is **never returned** by `negate`. The image of `negate` on
`[INT16_MIN, INT16_MAX]` excludes exactly `{−32767}`.

---

## Open Questions

1. **Design intent**: Was the `INT16_MAX → INT16_MIN` mapping intentional? The code
   comment does not explain it. Only `INT16_MIN → INT16_MAX` is strictly necessary to
   avoid UB. If the intended semantics is "negate with saturation", then
   `INT16_MAX → INT16_MAX` might be preferable and would restore injectivity.

2. **Usage sites**: Are there callers that assume `negate(negate(x)) == x`? If so,
   passing `x = −32767` would produce a silent wrong result (`−32768` instead of
   `−32767`).

3. **Alternative**: `INT16_MAX → −INT16_MAX = −32767` (mathematical negation) would
   make `negate` injective and surjective on `[INT16_MIN, INT16_MAX] ∖ {INT16_MIN}`,
   but then `negate(negate(INT16_MAX))` would chain correctly.

---

## Examples

| Input | Output | Notes |
|---|---|---|
| `32767` (`INT16_MAX`) | `−32768` (`INT16_MIN`) | Special case |
| `−32768` (`INT16_MIN`) | `32767` (`INT16_MAX`) | Avoids UB |
| `0` | `0` | Fixed point |
| `1` | `−1` | Typical |
| `−1` | `1` | Typical |
| `100` | `−100` | Typical |
| `−32767` | `32767` | **NOT** equal to `negate(negate(x))` restoring original |
