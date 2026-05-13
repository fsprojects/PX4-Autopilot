# NotchFilter — Informal Specification

🔬 *Lean Squad automated formal verification.*

**Target**: `math::NotchFilter<T>` — Direct Form I IIR notch filter
**C++ source**: `src/lib/mathlib/math/filter/NotchFilter.hpp`

---

## Purpose

`NotchFilter<T>` implements a second-order IIR notch (band-reject) filter using
Direct Form I. It attenuates a specific frequency (the notch frequency) while
passing all other frequencies with approximately unit gain.

The filter is used in PX4 to suppress motor vibration frequencies and other
narrow-band disturbances (e.g. in IMU signal processing, altitude control).

The key operation is `applyInternal(sample)` which takes one scalar (or vector)
sample and returns the filtered value, updating four delay elements.

---

## State

The filter maintains four delay elements:
- `_delay_element_1` (`x[n-1]`): previous input
- `_delay_element_2` (`x[n-2]`): input from two steps ago
- `_delay_element_output_1` (`y[n-1]`): previous output
- `_delay_element_output_2` (`y[n-2]`): output from two steps ago

And five coefficients (set via `setParameters` or `setCoefficients`):
- `b0, b1, b2`: feed-forward (numerator) coefficients
- `a1, a2`: feedback (denominator) coefficients (`a0` is normalised to 1)

---

## Preconditions

- Coefficients `b0, b1, b2, a1, a2` are finite (not NaN or ±∞).
- The filter has been initialised: `_initialized = true` (or `apply` handles
  the uninitialized case by calling `reset(sample)` first).
- Scalar type `T` supports +, -, *.

---

## Core Operation: `applyInternal(sample)`

```cpp
T output = b0*sample + b1*x1 + b2*x2 - a1*y1 - a2*y2;
x2 = x1;
x1 = sample;
y2 = y1;
y1 = output;
return output;
```

where `x1 = _delay_element_1`, `x2 = _delay_element_2`,
`y1 = _delay_element_output_1`, `y2 = _delay_element_output_2`.

---

## Postconditions

After one call to `applyInternal(sample)` with old state `(x1, x2, y1, y2)`:
1. **Output**: `output = b0*sample + b1*x1 + b2*x2 - a1*y1 - a2*y2`
2. **New x1**: `_delay_element_1 = sample`
3. **New x2**: `_delay_element_2 = x1` (old `_delay_element_1`)
4. **New y1**: `_delay_element_output_1 = output`
5. **New y2**: `_delay_element_output_2 = y1` (old `_delay_element_output_1`)

---

## Invariants

- Delay elements store the last two inputs and last two outputs respectively.
- The output is a linear combination of the current input and the four delay elements.

---

## Key Properties

### 1. Passthrough (disabled coefficients)

When `b0=1, b1=0, b2=0, a1=0, a2=0` (the "disabled" state):
```
output = sample
```
regardless of the delay elements.

### 2. Zero state → zero output

When all delay elements are zero and `sample = 0`:
```
output = 0
```

### 3. Linearity

The output and state transition are linear in `(sample, x1, x2, y1, y2)` for
fixed coefficients. Formally: if we scale all five by a constant `k`, the output
scales by `k` and the new state scales by `k` as well.

### 4. Delay element update correctness

The update `x2 ← x1; x1 ← sample` correctly shifts the input history.
The update `y2 ← y1; y1 ← output` correctly shifts the output history.

### 5. Reset initialisation

After `reset(sample)` (when `isFinite(sample)` holds):
- `x1 = x2 = sample`
- `y1 = y2 = sample * (b0 + b1 + b2) / (1 + a1 + a2)`

This initialises the filter to a plausible steady-state for the given sample
value, minimising start-up transients.

### 6. Steady-state consistency of reset

The reset formula is derived from the assumption that the filter is in DC steady
state at `sample`. At DC steady state: `output = sample` for a notch filter
(since the notch filter has unit DC gain). The reset satisfies:
```
y_ss = sample * (b0 + b1 + b2) / (1 + a1 + a2)
```
When `b0 + b1 + b2 = 1 + a1 + a2` (DC gain = 1), this simplifies to `y_ss = sample`.

---

## Edge Cases

- **Uninitialised filter**: `apply` calls `reset(sample)` on the first call,
  returning the reset output rather than a garbage value.
- **Non-finite sample in reset**: if `!isFinite(sample)`, the delay elements
  are zeroed. The output of the subsequent `applyInternal` will reflect zero state.
- **Disabled state** (`disable()`): sets all feedback/feed-forward coefficients to
  produce pass-through behaviour; `b0=1`, `b1=b2=a1=a2=0`. The filter passes
  input unchanged.
- **Coefficient-only update** (notch frequency change only): `b1` and `a1` are
  updated to `2 * beta * b0`; `b0, b2, a2` are unchanged. This is valid because
  the notch filter has symmetric numerator (`b0 = b2`) and the relationship
  `a1 = b1` holds (the notch property).

---

## Examples

### Passthrough example

Coefficients: `b0=1, b1=0, b2=0, a1=0, a2=0`.
State: `x1=5, x2=3, y1=5, y2=3`.
Input: `sample=7`.
```
output = 1*7 + 0*5 + 0*3 - 0*5 - 0*3 = 7
```

### Zero-state example

State: `x1=0, x2=0, y1=0, y2=0`.
Coefficients: any.
Input: `sample=0`.
```
output = b0*0 + b1*0 + b2*0 - a1*0 - a2*0 = 0
```

### Linearity example

If `(sample=2, x1=2, x2=2, y1=2, y2=2)` yields `output=2*k` for some `k`,
then `(sample=4, x1=4, x2=4, y1=4, y2=4)` yields `output=4*k`.

---

## Inferred Intent

The notch filter is designed to:
1. Suppress a narrow band of frequencies centred at `notch_freq`.
2. Pass all other frequencies (including DC) with unit gain.
3. Operate in Direct Form I (separate input and output delays) rather than
   Direct Form II, which makes it more numerically robust to coefficient changes.
4. Permit dynamic update of the notch frequency without resetting the filter
   history, by updating only `b1` and `a1` (since `b0 = b2` and `a1 = b1`).

---

## Open Questions

1. **DC gain = 1 requirement**: Is `b0 + b1 + b2 = 1 + a1 + a2` an invariant
   maintained by `setParameters`? Should be verified from the coefficient
   computation (`alpha`, `beta`, `a0_inv`).
2. **Stability**: The notch filter is stable when `|z-plane poles| < 1`. This
   is not checked at runtime after coefficient updates — should it be?
3. **Symmetric numerator**: The relationship `b0 = b2` is relied on for the
   frequency-only update path. Is this stated as a formal requirement? It holds
   from `setParameters` (`_b0 = a0_inv`, `_b2 = a0_inv`) but is not enforced
   by `setCoefficients`.
4. **Type `T`**: The filter is templated. Proofs are for scalar `T = Rat`. Vector
   extensions would require componentwise linearity.

---

## Approximations for Lean Modelling

- **Exact arithmetic**: use `Rat` (rationals) to avoid floating-point issues.
- **Coefficient computation** (`setParameters`): involves `tanf`, `cosf`, `sqrtf`.
  Out of scope for Lean proofs; coefficients taken as free parameters.
- **NaN/infinity handling**: omitted in the pure model; treated as unreachable.
- **Initialisation guard** (`_initialized`): omitted; model the pure `applyInternal`.
- **Vector `T`**: model only scalar `T = Rat`; the vector case follows by componentwise linearity.
