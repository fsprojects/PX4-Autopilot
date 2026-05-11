# Deadzone Correspondence Tests

🔬 *Lean Squad automated formal verification*

This directory contains **Route B correspondence tests** for the `deadzone` function,
validating that the Lean 4 rational model in
`formal-verification/lean/FVSquad/Deadzone.lean` matches the C++ template
implementation in `src/lib/mathlib/math/Functions.hpp`.

## Running the tests

```bash
python3 check_correspondence.py
```

Exit code 0 means all cases passed; non-zero means at least one mismatch.

## What is tested

| Test | Description |
|------|-------------|
| Zero deadzone | `deadzone(x, 0) = x` for all `x` |
| Inside deadzone | `\|x\| ≤ dz → deadzone(x, dz) = 0` |
| Positive branch | `x > dz ≥ 0 → deadzone(x, dz) = (x − dz) / (1 − dz)` |
| Negative branch | `x < −dz → deadzone(x, dz) = (x + dz) / (1 − dz)` |
| Boundary x=1 | `deadzone(1, dz) = 1` |
| Boundary x=−1 | `deadzone(−1, dz) = −1` |
| Odd symmetry | `deadzone(−x, dz) = −deadzone(x, dz)` |
| Monotone in value | `v₁ ≤ v₂ → deadzone(v₁, dz) ≤ deadzone(v₂, dz)` |
| Monotone in dz | `dz₁ ≤ dz₂ < x → deadzone(x, dz₂) ≤ deadzone(x, dz₁)` |
| Dense grid | All `(x, dz)` in `{-1, -0.9, …, 1} × {0, 0.1, …, 0.9}` |
| Rational fractions | Inputs like `1/3`, `2/7`, `3/11`, etc. |
| Output range | `-1 ≤ deadzone(x, dz) ≤ 1` |

## Domain assumptions

The C++ code clamps `value` to `[−1, 1]` and `dz` to `[0, 0.99]` before
computing. The Lean model abstracts away this clamping (it is a pre-condition
of the model). All test inputs are chosen within these bounds, so the C++
`constrain` calls are identity and the two sides compute the same thing.

## Correspondence theorem

For inputs in domain `x ∈ [−1, 1]`, `dz ∈ [0, 1)`:

```
C++:  out = (x − sign(x)·dz) / (1 − dz)  if |x| > dz, else 0
Lean: if x > dz  then (x − dz) / (1 − dz)
      elif x < −dz then (x + dz) / (1 − dz)
      else 0
```

These are equal because `sign(x) = 1` for `x ≥ 0` and `sign(x) = −1` for
`x < 0`, matching the Lean branching on `x > dz` vs `x < −dz`.
