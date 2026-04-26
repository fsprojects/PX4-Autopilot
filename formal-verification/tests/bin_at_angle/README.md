# ObstacleMath Bin-at-Angle Correspondence Tests

🔬 *Lean Squad automated formal verification.*

This directory contains Route B correspondence tests for the PX4 collision prevention
library, verifying that the Lean 4 integer model in
`formal-verification/lean/FVSquad/GetBinAtAngle.lean` produces results consistent
with the C++ implementation in `src/lib/collision_prevention/ObstacleMath.cpp`.

## What Is Tested

Three functions:

| C++ function | Lean model | Formula |
|---|---|---|
| `wrap_bin(bin, n)` | `wrapBin n bin` | `(bin + n) % n` (C++ integer arithmetic) |
| `get_bin_at_angle(bin_width, angle)` | `getBinI n k` | `k % n` (Euclidean modulo) |
| `get_offset_bin_index(bin, bin_width, angle_offset)` | `getOffsetBinI n b k` | `(b - k) % n` |

## Test Cases

- **wrap_bin (normal)**: 10 cases covering bin = 0, 1, n-1, n, n+1, -1, -n
- **wrap_bin (bug)**: 3 cases for `bin ≤ -n-1` demonstrating the latent C++ negative-index bug
- **get_bin_at_angle (10° bins, n=36)**: all 36 integer-aligned angles 0°–350°
- **get_bin_at_angle (5° bins, n=72)**: all 72 integer-aligned angles 0°–355°
- **get_bin_at_angle (45° bins, n=8)**: all 8 integer-aligned angles 0°–315°
- **get_bin_at_angle (2° bins, n=180)**: all 180 integer-aligned angles 0°–358°
- **Periodicity**: 8 cases verifying `angle + 360° = angle` for two bin widths
- **get_offset_bin_index**: 20 cases for n=36, bins b ∈ {0, 1, 10, 35}, offsets k ∈ {0, 1, 5, 18, 35}

**Total: 334 test cases.**

## Bug Demonstrated

The test script explicitly confirms the `wrap_bin` latent bug documented in
`WrapBin.lean` and `CORRESPONDENCE.md`:

```
cpp_wrap_bin(-37, 36) = -1  ← negative (BUG: used as array index → UB)
lean_wrapBin(36, -37) = 35  ← non-negative (correct intended behaviour)
```

The C++ formula `(bin + bin_count) % bin_count` uses truncated-toward-zero
`%` on signed `int`. For `bin + bin_count < 0` (i.e., `bin ≤ -n-1`), the result
is negative, which is incorrect for an array index. The Lean Euclidean model
always returns a value in `[0, n)`.

## Approach

The test script (`check_correspondence.py`) simulates both sides in Python:

- **C++ side**: uses Python integer arithmetic with explicit C++ truncation semantics
  for `%` on negative values (`int((bin + n) - n * int((bin + n) / n))`).
- **Lean model side**: uses Python's built-in `%`, which is Euclidean (same as
  Lean's `Int.emod` for positive divisors).

For integer-aligned angles (angle = k × bin_width, k ∈ ℤ), the Lean integer model
and the C++ implementation agree exactly — no floating-point rounding ambiguity.
The `round()` and `matrix::wrap()` pipeline in the C++ reduces to exact integer
arithmetic for these inputs.

## How to Run

```bash
cd formal-verification/tests/bin_at_angle
python3 check_correspondence.py
```

Expected output: `334/334 passed, 0 failed`

## Scope and Limitations

- **Integer-aligned inputs only**: the Lean model abstracts over `round()` rounding
  at half-bin boundaries. For angles that are not integer multiples of `bin_width`,
  the C++ and Lean results may differ by ±1 bin. This is documented as an
  "abstraction" in `CORRESPONDENCE.md`.
- **`get_lower_bound_angle`**: not tested here — its half-bin-unit model is covered
  by `GetLowerBoundAngle.lean`. No runnable correspondence tests exist yet for that function.
- **Float bin_width**: the test uses exact integer bin widths (10, 5, 45, 2 degrees).
  Non-integer bin widths are used in some PX4 configurations and are not tested.
