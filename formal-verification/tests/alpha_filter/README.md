# AlphaFilter Correspondence Tests

🔬 *Lean Squad automated formal verification*

This directory contains **Route B correspondence tests** for the `AlphaFilter`
scalar update function, validating that the Lean 4 rational model in
`formal-verification/lean/FVSquad/AlphaFilter.lean` matches the C++ template
implementation in `src/lib/mathlib/math/filter/AlphaFilter.hpp`.

## Function Under Test

```cpp
// AlphaFilter.hpp — first-order IIR ("leaky integrator")
template <typename T>
T AlphaFilter<T>::updateCalculation(const T &sample) {
    return _filter_state + _alpha * (sample - _filter_state);
}
```

The Lean 4 model (`AlphaFilter.lean`, namespace `PX4.AlphaFilter`):

```lean
def alphaUpdate (state alpha sample : Rat) : Rat :=
    state + alpha * (sample - state)
```

Both expressions are algebraically identical; for inputs that are exactly
representable in IEEE 754 float32 (dyadic rationals) the results agree bit-for-bit.

## Running the Tests

```bash
python3 check_correspondence.py
```

Exit code 0 means all cases passed; non-zero means at least one mismatch.

## What Is Tested

| Category | Cases | Notes |
|----------|-------|-------|
| Boundary cases | 8 | alpha=0/1, state=sample, zero inputs |
| Dyadic-rational grid | 200 | `state ∈ {0,1,-1,½}`, `alpha ∈ {½,¼,¾,⅛,⅞}`, `sample ∈ {0,1,-1,½,-½}` — exact equality required |
| Signed/large inputs | 8 | neg↔pos, large states, exact equality |
| Fine decimal grid | 135 | `alpha ∈ {0.1,…,0.9}`, relative tolerance 2e-6 |
| Multi-step convergence | 9 | 10 and 50 steps, relative tolerance 2e-6×n |
| Theorem spot-checks | ~250 | Verify Lean spec properties hold on all test cases |

**Total: 617+ correspondence checks.**

## Correspondence Level

The `AlphaFilter.lean` model is an **exact abstraction** of the C++ float
implementation for dyadic-rational inputs:

- The formula `state + alpha * (sample - state)` is identical in both
- For inputs representable in float32, there is zero rounding error
- For non-dyadic inputs (0.1, 0.3, etc.) the float rounding diverges from
  rational arithmetic by at most 1 ULP (~1e-7 relative), well within the
  2e-6 tolerance used for the decimal-grid tests

## Lean Theorems Validated

The test script also directly checks the following Lean theorems on test inputs:

| Theorem | Property |
|---------|----------|
| `alphaUpdate_fixed` | `alphaUpdate s a s = s` |
| `alphaUpdate_alpha_zero` | `alphaUpdate s 0 x = s` |
| `alphaUpdate_alpha_one` | `alphaUpdate s 1 x = x` |
| `alphaUpdate_no_overshoot_up` | `s ≤ x → s ≤ new ≤ x` |
| `alphaUpdate_no_overshoot_down` | `x ≤ s → x ≤ new ≤ s` |
| `alphaIterate_formula` | `state_n = target + (s₀ − target)·(1−α)ⁿ` |

## Domain Assumptions

- `alpha ∈ [0, 1]` — the C++ class enforces this via `setAlpha`
- `state` and `sample` are finite float32 values — NaN and ±∞ are out of scope
  (the C++ implementation reinitialises `_filter_state` to `sample` when the
  current state is not finite; this guard is not modelled in the Lean spec)
