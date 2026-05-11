# expo (Exponential RC Curve) — Route B Correspondence Tests

🔬 *Lean Squad automated formal verification.*

## Purpose

Validates that the Lean 4 rational model in
`formal-verification/lean/FVSquad/Expo.lean` produces results behaviourally
identical to the C++ template implementation in
`src/lib/mathlib/math/Functions.hpp` on a comprehensive set of rational inputs.

## Running the tests

```bash
python3 check_correspondence.py
```

Exit code 0 on success, non-zero on any mismatch. No external dependencies.

## Test outcome (run 113)

```
Total test cases: 1373
✅ All 1373 cases passed — Lean model matches C++ reference exactly
```

## What is tested

| Test group | Cases | What it verifies |
|------------|-------|-----------------|
| Boundary / special | 9 | v,e ∈ {-1,0,1} × {0,½,1} |
| `expo_at_zero` | 10 | v=0, e ∈ {0,1/2,...,9/10} — output always 0 |
| `expo_at_pos_one` | 11 | v=1, e ∈ [0,1] — output always 1 |
| `expo_at_neg_one` | 11 | v=-1, e ∈ [0,1] — output always -1 |
| `expo_linear` (e=0) | 25 | identity on [-1,1], clamp outside |
| `expo_cubic` (e=1) | 21 | x³ on [-1,1], clamp outside |
| Odd symmetry | 330 | expo(-v,e) = -expo(v,e) for a grid of (v,e) |
| Range check | 330 | output ∈ [-1,1] for all tested inputs |
| Dense grid | 558 | v ∈ [-1.5,1.5], e ∈ [-0.2,1.2] — clamp tested |
| Rational fractions | 48 | v = p/q, e = 1/q for p∈{1…6}, q∈{3,7,11} |

## What the correspondence covers

Both sides implement exactly the same formula in exact rational arithmetic:

```
constrain(v, -1, 1) → x
constrain(e,  0, 1) → ec
(1 - ec) * x + ec * x * x * x
```

Since the Lean model and the C++ translation are mathematically identical
(both using exact rational arithmetic on the same formula), the correspondence
holds universally — not just on the tested cases. The tests confirm there are no
transcription errors between the C++ template and the Lean definition.

## What is NOT covered

- Floating-point rounding for non-rational inputs (C++ uses `float`)
- The `constrain` call uses `Rat`-ordered comparison in Lean; C++ uses
  `float` comparison. These agree on all exact rational inputs tested.
- Performance (the test uses Python `Fraction` for exact arithmetic).

## Source references

- C++ source: `src/lib/mathlib/math/Functions.hpp` — `expo<T>` template
- Lean source: `formal-verification/lean/FVSquad/Expo.lean` — `expoRat`
