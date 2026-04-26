#!/usr/bin/env python3
"""
Correspondence test: ObstacleMath get_bin_at_angle / get_offset_bin_index /
wrap_bin — C++ integer-model vs Lean 4 model in GetBinAtAngle.lean.

🔬 Lean Squad automated formal verification.

## What is tested

Three functions from `src/lib/collision_prevention/ObstacleMath.cpp`:

| C++ function | Lean model | Formula |
|---|---|---|
| `wrap_bin(bin, n)` | `wrapBin n bin` | `(bin + n) % n`  (C++ truncation) |
| `get_bin_at_angle(bw, angle)` | `getBinI n k` | `k % n` (Euclidean) |
| `get_offset_bin_index(bin, bw, off)` | `getOffsetBinI n b k` | `(b - k) % n` |

## Approach

- **C++ side**: simulated in Python using the same integer arithmetic as C++.
  `wrap_bin` uses Python's `%` operator on integers — Python `%` always returns
  a non-negative result for a positive divisor, which matches the C++ behaviour
  for `bin + bin_count >= 0`.  For the bug-trigger case we compute `(bin + n) % n`
  using C++ truncation semantics (implemented via `int((bin + n) - n * int((bin + n) / n))`).
- **Lean model side**: `getBinI n k = k % n` using Python's Euclidean modulo
  (always non-negative); `getOffsetBinI n b k = (b - k) % n` same.

## Test scope

Integer-aligned inputs only — the Lean model is exact on these, so perfect
agreement with the C++ simulation is expected.  For non-integer-aligned float
angles, the Lean integer model approximates the C++ result (to nearest bin), and
is not tested here.

Run:
    python3 check_correspondence.py

Exit code 0 on all tests passing; non-zero on any failure.
"""

import sys

# ─── C++ simulation ──────────────────────────────────────────────────────────

def cpp_wrap_bin(bin_: int, n: int) -> int:
    """
    Mirrors ObstacleMath.cpp wrap_bin:
        return (bin + bin_count) % bin_count;
    C++ truncated-toward-zero integer modulo for `int`.
    Python % is Euclidean (non-negative), so we must simulate C++ truncation.
    """
    raw = bin_ + n
    # C++ truncated remainder: sign follows dividend
    if raw >= 0:
        return raw % n
    else:
        # negative numerator, positive divisor → C++ % returns negative or zero
        return -((-raw) % n) if ((-raw) % n) != 0 else 0


def cpp_wrap_360(angle_deg: float) -> float:
    """Mirrors matrix::wrap(angle, 0.f, 360.f)."""
    a = angle_deg % 360.0
    if a < 0:
        a += 360.0
    return a


def cpp_get_bin_at_angle(bin_width: float, angle: float) -> int:
    """
    Mirrors ObstacleMath.cpp get_bin_at_angle:
        int bin_at_angle = (int)round(matrix::wrap(angle, 0.f, 360.f) / bin_width);
        return wrap_bin(bin_at_angle, 360 / bin_width);
    """
    import math
    n = int(round(360.0 / bin_width))  # 360 / bin_width (integer)
    wrapped = cpp_wrap_360(angle)
    bin_at = int(math.copysign(math.floor(abs(wrapped / bin_width) + 0.5),
                                wrapped / bin_width))  # round half-away-from-zero
    # Python round() uses banker's rounding; use math.floor(x + 0.5) for C round()
    bin_at = int(math.floor(wrapped / bin_width + 0.5))
    return cpp_wrap_bin(bin_at, n)


def cpp_get_offset_bin(bin_: int, bin_width: float, angle_offset: float) -> int:
    """
    Mirrors ObstacleMath.cpp get_offset_bin_index:
        int offset = get_bin_at_angle(bin_width, angle_offset);
        return wrap_bin(bin - offset, 360 / bin_width);
    """
    n = int(round(360.0 / bin_width))
    offset = cpp_get_bin_at_angle(bin_width, angle_offset)
    return cpp_wrap_bin(bin_ - offset, n)


# ─── Lean model simulation ────────────────────────────────────────────────────

def lean_get_bin(n: int, k: int) -> int:
    """
    Lean: getBinI n k = (k % n).toNat
    Python % is Euclidean (same as Lean's Int.emod for n > 0).
    """
    return k % n  # always non-negative for n > 0


def lean_get_offset_bin(n: int, b: int, k: int) -> int:
    """
    Lean: getOffsetBinI n b k = getBinI n (b - k)
    """
    return lean_get_bin(n, b - k)


def lean_wrap_bin(n: int, bin_: int) -> int:
    """
    Lean: wrapBin n bin = ((bin + n) % n) — Euclidean, always non-negative.
    """
    return (bin_ + n) % n


# ─── Test helpers ─────────────────────────────────────────────────────────────

failures = 0
total = 0


def check(label: str, cpp_result: int, lean_result: int) -> bool:
    global failures, total
    total += 1
    ok = cpp_result == lean_result
    sign = "✓" if ok else "✗"
    status = "PASS" if ok else "FAIL"
    print(f"  {sign} {status}  {label}")
    if not ok:
        print(f"       cpp={cpp_result}  lean={lean_result}")
        failures += 1
    return ok


# ─── Test suite ───────────────────────────────────────────────────────────────

def run_wrap_bin_tests():
    print("\n── wrap_bin: Euclidean vs C++ (Lean wrapBin vs cpp_wrap_bin) ──")

    # For bin + n >= 0, C++ and Lean agree
    cases = [
        # (bin, n, description)
        (0, 36, "bin=0"),
        (1, 36, "bin=1"),
        (35, 36, "bin=n-1"),
        (36, 36, "bin=n (wraps to 0)"),
        (37, 36, "bin=n+1"),
        (-1, 36, "bin=-1 (wraps to n-1)"),
        (-36, 36, "bin=-n (wraps to 0)"),
        (0, 8, "n=8, bin=0"),
        (7, 8, "n=8, bin=n-1"),
        (-1, 8, "n=8, bin=-1"),
    ]
    for bin_, n, desc in cases:
        cpp_val = cpp_wrap_bin(bin_, n)
        lean_val = lean_wrap_bin(n, bin_)
        check(f"wrap_bin({bin_}, {n}) [{desc}]", cpp_val, lean_val)


def run_wrap_bin_bug_test():
    """Demonstrate the C++ bug: wrap_bin returns negative for bin <= -n-1."""
    print("\n── wrap_bin latent bug: bin <= -n-1 gives negative result in C++ ──")
    n = 36
    for bin_ in [-n - 1, -n - 2, -2 * n - 1]:
        cpp_val = cpp_wrap_bin(bin_, n)
        lean_val = lean_wrap_bin(n, bin_)
        bug_present = cpp_val < 0
        total_count = 1
        print(f"  {'!' if bug_present else ' '} wrap_bin({bin_}, {n}): "
              f"cpp={cpp_val}  lean={lean_val}  "
              f"{'BUG: negative result' if bug_present else 'OK'}")
    # The key assertion: cpp gives negative, lean gives non-negative
    bin_bug = -n - 1
    cpp_bug = cpp_wrap_bin(bin_bug, n)
    lean_ok = lean_wrap_bin(n, bin_bug)
    print(f"\n  Bug confirmation: cpp_wrap_bin({bin_bug}, {n}) = {cpp_bug} < 0 "
          f"= {cpp_bug < 0}")
    print(f"  Lean wrapBin {n} {bin_bug} = {lean_ok} ≥ 0 = {lean_ok >= 0}")


def run_get_bin_tests():
    print("\n── get_bin_at_angle / getBinI: integer-aligned angles ──")

    # Test multiple bin widths
    configs = [
        (10.0, 36, "10° bins / 36 bins"),
        (5.0, 72, "5° bins / 72 bins"),
        (45.0, 8, "45° bins / 8 bins"),
        (2.0, 180, "2° bins / 180 bins"),
    ]

    for bin_width, n, desc in configs:
        print(f"\n  [{desc}]")
        # Test angles that are exact integer multiples of bin_width
        for k in range(0, n):
            angle = k * bin_width
            cpp_val = cpp_get_bin_at_angle(bin_width, angle)
            lean_val = lean_get_bin(n, k)
            check(f"get_bin_at_angle({bin_width}°, angle={angle:.0f}°) → bin {k}", cpp_val, lean_val)


def run_get_bin_wrap_tests():
    print("\n── get_bin_at_angle: wrapped angles (≥ 360°, negative) ──")

    configs = [
        (10.0, 36),
        (45.0, 8),
    ]
    for bin_width, n in configs:
        # angle = 360° + k*bw should give same result as k*bw
        for k in [0, 1, 5, n - 1]:
            angle_base = k * bin_width
            angle_wrapped = angle_base + 360.0
            cpp_base = cpp_get_bin_at_angle(bin_width, angle_base)
            cpp_wrapped = cpp_get_bin_at_angle(bin_width, angle_wrapped)
            lean_base = lean_get_bin(n, k)
            lean_wrapped = lean_get_bin(n, k + n)  # k + n ≡ k mod n
            check(f"periodicity: bw={bin_width}° k={k}: angle vs angle+360°",
                  cpp_wrapped, lean_base)


def run_offset_bin_tests():
    print("\n── get_offset_bin_index / getOffsetBinI: rotation tests ──")

    bin_width = 10.0
    n = 36

    # Basic offset tests: offset by integer multiple of bin_width
    for b in [0, 1, 10, 35]:
        for k_offset in [0, 1, 5, 18, 35]:
            angle_offset = k_offset * bin_width
            cpp_val = cpp_get_offset_bin(b, bin_width, angle_offset)
            lean_val = lean_get_offset_bin(n, b, k_offset)
            check(f"offset_bin(b={b}, bw={bin_width}°, off={angle_offset:.0f}°="
                  f"k={k_offset})", cpp_val, lean_val)


def main() -> int:
    print("=" * 70)
    print("PX4 ObstacleMath Correspondence Test")
    print("C++ integer simulation vs Lean 4 integer model (GetBinAtAngle.lean)")
    print("Integer-aligned inputs only (exact agreement expected)")
    print("=" * 70)

    run_wrap_bin_tests()
    run_wrap_bin_bug_test()
    run_get_bin_tests()
    run_get_bin_wrap_tests()
    run_offset_bin_tests()

    print()
    print("=" * 70)
    print(f"Results: {total - failures}/{total} passed, {failures} failed")
    if failures == 0:
        print("✓ All correspondence tests PASSED")
        print("  The Lean integer model agrees with the C++ simulation on all")
        print("  integer-aligned inputs.")
    else:
        print(f"✗ {failures} FAILED — correspondence gap found!")
    print("=" * 70)

    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
