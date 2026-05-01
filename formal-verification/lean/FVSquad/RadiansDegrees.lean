/-!
# PX4 `math::radians` / `math::degrees` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::radians` and
`math::degrees` from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Limits.hpp` (lines 97–106)
- **Informal spec**: `formal-verification/specs/radians_degrees_informal.md`

## C++ Reference

```cpp
template<typename T>
constexpr T radians(T degrees) {
    return degrees * (static_cast<T>(MATH_PI) / static_cast<T>(180));
}

template<typename T>
constexpr T degrees(T radians) {
    return radians * (static_cast<T>(180) / static_cast<T>(MATH_PI));
}
```

where `MATH_PI ~= 3.14159265358979323846`.

## Model

We work over `Rat` (rational numbers) for exact arithmetic, parameterising over an
abstract `pi : Rat` satisfying only `pi > 0`.  This captures all algebraic properties
(linearity, round-trip, monotonicity) without committing to a specific numeric
approximation of pi.

```
radiansQ x := x * (pi / 180)
degreesQ x := x * (180 / pi)
```

## Approximations / Out of Scope

- **IEEE 754 float semantics**: rounding, NaN, and infinity are not modelled.  In
  particular the round-trip `degrees(radians(x))` accumulates two rounding errors
  over `float`; the Lean spec captures the exact-arithmetic ideal.
- **Integer `T`**: with `T = int`, the C++ expression `MATH_PI / 180` truncates to
  `0`, making both functions return 0 for all inputs.  The `Rat` model does not
  exhibit this silent truncation bug; it is flagged in the informal spec.
- **`MATH_PI` vs `M_PI`**: platform-specific constant choice not modelled.

## Theorems Summary

| Theorem | Description | Status |
|---------|-------------|--------|
| `radiansQ_zero` | `radians(0) = 0` | Proved |
| `degreesQ_zero` | `degrees(0) = 0` | Proved |
| `radiansQ_add` | `radians(a+b) = radians(a)+radians(b)` | Proved |
| `degreesQ_add` | `degrees(a+b) = degrees(a)+degrees(b)` | Proved |
| `radiansQ_smul` | `radians(k*x) = k * radians(x)` | Proved |
| `degreesQ_smul` | `degrees(k*x) = k * degrees(x)` | Proved |
| `radiansQ_neg` | `radians(-x) = -radians(x)` | Proved |
| `degreesQ_neg` | `degrees(-x) = -degrees(x)` | Proved |
| `radiansQ_strict_mono` | `a < b -> radians(a) < radians(b)` | Proved |
| `degreesQ_strict_mono` | `a < b -> degrees(a) < degrees(b)` | Proved |
| `radiansQ_mono` | `a <= b -> radians(a) <= radians(b)` | Proved |
| `degreesQ_mono` | `a <= b -> degrees(a) <= degrees(b)` | Proved |
| `radiansQ_pos` | `0 < x -> 0 < radians(x)` | Proved |
| `degreesQ_pos` | `0 < x -> 0 < degrees(x)` | Proved |
| `radiansQ_neg_input` | `x < 0 -> radians(x) < 0` | Proved |
| `degreesQ_neg_input` | `x < 0 -> degrees(x) < 0` | Proved |
| `radiansQ_injective` | `radians` is injective | Proved |
| `degreesQ_injective` | `degrees` is injective | Proved |
| `degreesQ_radiansQ` | `degrees(radians(x)) = x` | Proved |
| `radiansQ_degreesQ` | `radians(degrees(x)) = x` | Proved |
| `radiansQ_180` | `radians(180) = pi` | Proved |
| `radiansQ_360` | `radians(360) = 2*pi` | Proved |
| `radiansQ_90` | `radians(90) = pi/2` | Proved |
| `radiansQ_neg180` | `radians(-180) = -pi` | Proved |
| `degreesQ_pi` | `degrees(pi) = 180` | Proved |
| `degreesQ_pi_div_2` | `degrees(pi/2) = 90` | Proved |
| `degreesQ_two_pi` | `degrees(2*pi) = 360` | Proved |
| `degreesQ_neg_pi` | `degrees(-pi) = -180` | Proved |
-/

namespace PX4.RadiansDegrees

-- ============================================================
-- Abstract pi parameter
-- ============================================================

/-- Abstract placeholder for pi; we only need positivity. -/
axiom pi : Rat
axiom pi_pos : (0 : Rat) < pi

/-- Derived: pi is not zero. -/
theorem pi_ne_zero : pi ≠ 0 := Rat.ne_of_gt pi_pos

private theorem _180_ne_zero : (180 : Rat) ≠ 0 := by native_decide

/-- Derived: pi / 180 > 0. -/
theorem pi_div_180_pos : (0 : Rat) < pi / 180 := by
  rw [Rat.div_def]
  exact Rat.mul_pos pi_pos (Rat.inv_pos.mpr (by native_decide))

/-- Derived: 180 / pi > 0 (needed for degrees-to-radians monotonicity). -/
theorem inv_pi_pos : (0 : Rat) < 180 / pi := by
  rw [Rat.div_def]
  exact Rat.mul_pos (by native_decide) (Rat.inv_pos.mpr pi_pos)

-- ============================================================
-- Function definitions
-- ============================================================

/-- Pure rational model of `math::radians`: multiply by pi/180. -/
noncomputable def radiansQ (x : Rat) : Rat := x * (pi / 180)

/-- Pure rational model of `math::degrees`: multiply by 180/pi. -/
noncomputable def degreesQ (x : Rat) : Rat := x * (180 / pi)

-- ============================================================
-- Section 1: Fixed point at zero
-- ============================================================

/-- `radians(0) = 0`. -/
@[simp]
theorem radiansQ_zero : radiansQ 0 = 0 := by
  simp [radiansQ]

/-- `degrees(0) = 0`. -/
@[simp]
theorem degreesQ_zero : degreesQ 0 = 0 := by
  simp [degreesQ]

-- ============================================================
-- Section 2: Linearity (additivity and scaling)
-- ============================================================

/-- `radians` is additive: `radians(a + b) = radians(a) + radians(b)`. -/
theorem radiansQ_add (a b : Rat) :
    radiansQ (a + b) = radiansQ a + radiansQ b := by
  simp only [radiansQ, Rat.add_mul]

/-- `degrees` is additive: `degrees(a + b) = degrees(a) + degrees(b)`. -/
theorem degreesQ_add (a b : Rat) :
    degreesQ (a + b) = degreesQ a + degreesQ b := by
  simp only [degreesQ, Rat.add_mul]

/-- `radians` scales: `radians(k * x) = k * radians(x)`. -/
theorem radiansQ_smul (k x : Rat) : radiansQ (k * x) = k * radiansQ x := by
  simp only [radiansQ]; rw [Rat.mul_assoc]

/-- `degrees` scales: `degrees(k * x) = k * degrees(x)`. -/
theorem degreesQ_smul (k x : Rat) : degreesQ (k * x) = k * degreesQ x := by
  simp only [degreesQ]; rw [Rat.mul_assoc]

/-- `radians` negates: `radians(-x) = -radians(x)`. -/
theorem radiansQ_neg (x : Rat) : radiansQ (-x) = -radiansQ x := by
  simp only [radiansQ, Rat.neg_mul]

/-- `degrees` negates: `degrees(-x) = -degrees(x)`. -/
theorem degreesQ_neg (x : Rat) : degreesQ (-x) = -degreesQ x := by
  simp only [degreesQ, Rat.neg_mul]

-- ============================================================
-- Section 3: Strict monotonicity and sign preservation
-- ============================================================

/-- `radians` is strictly monotone: `a < b -> radians(a) < radians(b)`. -/
theorem radiansQ_strict_mono {a b : Rat} (h : a < b) : radiansQ a < radiansQ b := by
  simp only [radiansQ]
  exact Rat.mul_lt_mul_of_pos_right h pi_div_180_pos

/-- `degrees` is strictly monotone: `a < b -> degrees(a) < degrees(b)`. -/
theorem degreesQ_strict_mono {a b : Rat} (h : a < b) : degreesQ a < degreesQ b := by
  simp only [degreesQ]
  exact Rat.mul_lt_mul_of_pos_right h inv_pi_pos

/-- `radians` is weakly monotone: `a <= b -> radians(a) <= radians(b)`. -/
theorem radiansQ_mono {a b : Rat} (h : a ≤ b) : radiansQ a ≤ radiansQ b := by
  simp only [radiansQ]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt pi_div_180_pos)

/-- `degrees` is weakly monotone: `a <= b -> degrees(a) <= degrees(b)`. -/
theorem degreesQ_mono {a b : Rat} (h : a ≤ b) : degreesQ a ≤ degreesQ b := by
  simp only [degreesQ]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt inv_pi_pos)

/-- Sign preservation for `radians`: positive input gives positive output. -/
theorem radiansQ_pos {x : Rat} (hx : 0 < x) : 0 < radiansQ x :=
  radiansQ_zero ▸ radiansQ_strict_mono hx

/-- Sign preservation for `radians`: negative input gives negative output. -/
theorem radiansQ_neg_input {x : Rat} (hx : x < 0) : radiansQ x < 0 :=
  radiansQ_zero ▸ radiansQ_strict_mono hx

/-- Sign preservation for `degrees`: positive input gives positive output. -/
theorem degreesQ_pos {x : Rat} (hx : 0 < x) : 0 < degreesQ x :=
  degreesQ_zero ▸ degreesQ_strict_mono hx

/-- Sign preservation for `degrees`: negative input gives negative output. -/
theorem degreesQ_neg_input {x : Rat} (hx : x < 0) : degreesQ x < 0 :=
  degreesQ_zero ▸ degreesQ_strict_mono hx

-- ============================================================
-- Section 4: Injectivity
-- ============================================================

/-- `radians` is injective (follows from strict monotonicity). -/
theorem radiansQ_injective : Function.Injective radiansQ := by
  intro a b h
  simp only [radiansQ] at h
  have hpi180 : pi / 180 ≠ 0 := Rat.ne_of_gt pi_div_180_pos
  have key : a * (pi / 180) * (pi / 180)⁻¹ = b * (pi / 180) * (pi / 180)⁻¹ :=
    congrArg (· * (pi / 180)⁻¹) h
  rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hpi180, Rat.mul_one,
      Rat.mul_assoc, Rat.mul_inv_cancel _ hpi180, Rat.mul_one] at key
  exact key

/-- `degrees` is injective. -/
theorem degreesQ_injective : Function.Injective degreesQ := by
  intro a b h
  simp only [degreesQ] at h
  have h180pi : (180 : Rat) / pi ≠ 0 := Rat.ne_of_gt inv_pi_pos
  have key : a * (180 / pi) * (180 / pi)⁻¹ = b * (180 / pi) * (180 / pi)⁻¹ :=
    congrArg (· * (180 / pi)⁻¹) h
  rw [Rat.mul_assoc, Rat.mul_inv_cancel _ h180pi, Rat.mul_one,
      Rat.mul_assoc, Rat.mul_inv_cancel _ h180pi, Rat.mul_one] at key
  exact key

-- ============================================================
-- Section 5: Round-trip (mutual inverse)
-- ============================================================

private theorem pi_div_180_mul_inv : pi / 180 * (180 / pi) = 1 := by
  rw [Rat.div_def, Rat.div_def]
  rw [Rat.mul_comm pi 180⁻¹, Rat.mul_comm 180 pi⁻¹]
  rw [Rat.mul_assoc, ← Rat.mul_assoc pi pi⁻¹]
  rw [Rat.mul_inv_cancel _ pi_ne_zero, Rat.one_mul]
  rw [Rat.inv_mul_cancel _ _180_ne_zero]

private theorem inv_pi_mul_pi_div : 180 / pi * (pi / 180) = 1 := by
  rw [Rat.mul_comm]; exact pi_div_180_mul_inv

/-- `degrees(radians(x)) = x` for all `x` (exact rational arithmetic). -/
theorem degreesQ_radiansQ (x : Rat) : degreesQ (radiansQ x) = x := by
  simp only [degreesQ, radiansQ]
  rw [Rat.mul_assoc, pi_div_180_mul_inv, Rat.mul_one]

/-- `radians(degrees(x)) = x` for all `x` (exact rational arithmetic). -/
theorem radiansQ_degreesQ (x : Rat) : radiansQ (degreesQ x) = x := by
  simp only [degreesQ, radiansQ]
  rw [Rat.mul_assoc, inv_pi_mul_pi_div, Rat.mul_one]

/-- `radians` and `degrees` are left-inverses of each other. -/
theorem radiansQ_leftInverse : Function.LeftInverse radiansQ degreesQ :=
  radiansQ_degreesQ

/-- `degrees` and `radians` are left-inverses of each other. -/
theorem degreesQ_leftInverse : Function.LeftInverse degreesQ radiansQ :=
  degreesQ_radiansQ

-- ============================================================
-- Section 6: Specific values
-- ============================================================

/-- Auxiliary: 360 / 180 = 2. -/
private theorem _360_div_180 : (360 : Rat) * 180⁻¹ = 2 := by native_decide

/-- Auxiliary: 90 / 180 = 1/2. -/
private theorem _90_div_180 : (90 : Rat) * 180⁻¹ = 2⁻¹ := by native_decide

/-- Auxiliary: 180 / 2 = 90. -/
private theorem _180_div_2 : (180 : Rat) * 2⁻¹ = 90 := by native_decide

/-- Auxiliary: 2 * 180 = 360. -/
private theorem _2_mul_180 : (2 : Rat) * 180 = 360 := by native_decide

/-- `radians(180) = pi`. -/
theorem radiansQ_180 : radiansQ 180 = pi := by
  simp only [radiansQ, Rat.div_def]
  calc (180 : Rat) * (pi * 180⁻¹)
      = 180 * pi * 180⁻¹   := (Rat.mul_assoc 180 pi 180⁻¹).symm
    _ = pi * 180 * 180⁻¹   := by rw [Rat.mul_comm 180 pi]
    _ = pi * (180 * 180⁻¹) := Rat.mul_assoc pi 180 180⁻¹
    _ = pi * 1             := by rw [Rat.mul_inv_cancel _ _180_ne_zero]
    _ = pi                 := Rat.mul_one pi

/-- `radians(360) = 2 * pi`. -/
theorem radiansQ_360 : radiansQ 360 = 2 * pi := by
  simp only [radiansQ, Rat.div_def]
  calc (360 : Rat) * (pi * 180⁻¹)
      = 360 * pi * 180⁻¹   := (Rat.mul_assoc 360 pi 180⁻¹).symm
    _ = pi * 360 * 180⁻¹   := by rw [Rat.mul_comm 360 pi]
    _ = pi * (360 * 180⁻¹) := Rat.mul_assoc pi 360 180⁻¹
    _ = pi * 2             := by rw [_360_div_180]
    _ = 2 * pi             := Rat.mul_comm pi 2

/-- `radians(90) = pi / 2`. -/
theorem radiansQ_90 : radiansQ 90 = pi / 2 := by
  simp only [radiansQ, Rat.div_def]
  calc (90 : Rat) * (pi * 180⁻¹)
      = 90 * pi * 180⁻¹   := (Rat.mul_assoc 90 pi 180⁻¹).symm
    _ = pi * 90 * 180⁻¹   := by rw [Rat.mul_comm 90 pi]
    _ = pi * (90 * 180⁻¹) := Rat.mul_assoc pi 90 180⁻¹
    _ = pi * 2⁻¹           := by rw [_90_div_180]

/-- `radians(-180) = -pi`. -/
theorem radiansQ_neg180 : radiansQ (-180) = -pi := by
  rw [radiansQ_neg, radiansQ_180]

/-- `degrees(pi) = 180`. -/
theorem degreesQ_pi : degreesQ pi = 180 := by
  simp only [degreesQ, Rat.div_def]
  calc pi * (180 * pi⁻¹)
      = pi * 180 * pi⁻¹   := (Rat.mul_assoc pi 180 pi⁻¹).symm
    _ = 180 * pi * pi⁻¹   := by rw [Rat.mul_comm pi 180]
    _ = 180 * (pi * pi⁻¹) := Rat.mul_assoc 180 pi pi⁻¹
    _ = 180 * 1           := by rw [Rat.mul_inv_cancel _ pi_ne_zero]
    _ = 180               := Rat.mul_one 180

/-- `degrees(pi / 2) = 90`. -/
theorem degreesQ_pi_div_2 : degreesQ (pi / 2) = 90 := by
  simp only [degreesQ, Rat.div_def]
  calc pi * 2⁻¹ * (180 * pi⁻¹)
      = pi * (2⁻¹ * (180 * pi⁻¹)) := Rat.mul_assoc pi 2⁻¹ (180 * pi⁻¹)
    _ = pi * (2⁻¹ * 180 * pi⁻¹)  := by rw [← Rat.mul_assoc 2⁻¹]
    _ = pi * (180 * 2⁻¹ * pi⁻¹)  := by rw [Rat.mul_comm 2⁻¹ 180]
    _ = pi * (180 * (2⁻¹ * pi⁻¹)) := by rw [Rat.mul_assoc 180]
    _ = pi * (180 * (pi⁻¹ * 2⁻¹)) := by rw [Rat.mul_comm 2⁻¹ pi⁻¹]
    _ = pi * (180 * pi⁻¹ * 2⁻¹)  := by rw [← Rat.mul_assoc 180]
    _ = (pi * (180 * pi⁻¹)) * 2⁻¹ := (Rat.mul_assoc pi (180 * pi⁻¹) 2⁻¹).symm
    _ = (pi * 180 * pi⁻¹) * 2⁻¹  := by rw [Rat.mul_assoc pi 180]
    _ = (180 * pi * pi⁻¹) * 2⁻¹  := by rw [Rat.mul_comm pi 180]
    _ = (180 * (pi * pi⁻¹)) * 2⁻¹ := by rw [Rat.mul_assoc 180]
    _ = (180 * 1) * 2⁻¹           := by rw [Rat.mul_inv_cancel _ pi_ne_zero]
    _ = 180 * 2⁻¹                 := by rw [Rat.mul_one]
    _ = 90                        := _180_div_2

/-- `degrees(2 * pi) = 360`. -/
theorem degreesQ_two_pi : degreesQ (2 * pi) = 360 := by
  simp only [degreesQ, Rat.div_def]
  calc (2 * pi) * (180 * pi⁻¹)
      = 2 * (pi * (180 * pi⁻¹)) := Rat.mul_assoc 2 pi (180 * pi⁻¹)
    _ = 2 * (pi * 180 * pi⁻¹)  := by rw [Rat.mul_assoc pi]
    _ = 2 * (180 * pi * pi⁻¹)  := by rw [Rat.mul_comm pi 180]
    _ = 2 * (180 * (pi * pi⁻¹)) := by rw [Rat.mul_assoc 180]
    _ = 2 * (180 * 1)           := by rw [Rat.mul_inv_cancel _ pi_ne_zero]
    _ = 2 * 180                 := by rw [Rat.mul_one]
    _ = 360                     := _2_mul_180

/-- `degrees(-pi) = -180`. -/
theorem degreesQ_neg_pi : degreesQ (-pi) = -180 := by
  rw [degreesQ_neg, degreesQ_pi]

-- ============================================================
-- Section 7: Composition properties
-- ============================================================

/-- Chaining: `radians(degrees(radians(x))) = radians(x)`. -/
theorem radiansQ_degreesQ_radiansQ (x : Rat) :
    radiansQ (degreesQ (radiansQ x)) = radiansQ x :=
  radiansQ_degreesQ (radiansQ x)

/-- `radians ∘ degrees = id`. -/
theorem radiansQ_comp_degreesQ : radiansQ ∘ degreesQ = id := by
  funext x; simp [Function.comp, radiansQ_degreesQ]

/-- `degrees ∘ radians = id`. -/
theorem degreesQ_comp_radiansQ : degreesQ ∘ radiansQ = id := by
  funext x; simp [Function.comp, degreesQ_radiansQ]

end PX4.RadiansDegrees
