/-!
# PX4 `BlockIntegralTrap` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of PX4's trapezoidal
integrator-with-saturation `BlockIntegralTrap`:

- **C++ source**: `src/lib/controllib/BlockIntegralTrap.cpp` (lines 47–53) and
  `src/lib/controllib/BlockIntegralTrap.hpp` (lines 72–100)

## C++ Source

```cpp
float BlockIntegralTrap::update(float input)
{
    // trapezoidal integration
    setY(_limit.update(getY() +
              (getU() + input) / 2.0f * getDt()));
    setU(input);
    return getY();
}
```

`_limit` is a `BlockLimitSym` clamping to `[-max, max]`.

## Model

Over `Rat` (exact rational arithmetic):
- **State** (`ITState`): `y` (integrator output) and `u` (previous input)
- **Parameters** (`ITParams`): `dt` (timestep) and `limit` (symmetric saturation bound ≥ 0)
- **Update** (`itUpdate`): trapezoidal accumulation with saturation

## Approximations / out of scope

- IEEE 754 rounding, NaN, ±∞ not modelled.
- `Block` base class (`getDt`, `getMax`) modelled as direct parameters.
- Full BIBO stability (pole analysis) is out of scope.
-/

namespace PX4.BlockIntegralTrap

-- ============================================================
-- § 0  Helpers (constrain over Rat)
-- ============================================================

/-- Rational constrain: clamp `v` to `[lo, hi]`. -/
def rConstrain (v lo hi : Rat) : Rat :=
  if v < lo then lo else if v > hi then hi else v

theorem rConstrain_ge (v lo hi : Rat) (h : lo ≤ hi) : lo ≤ rConstrain v lo hi := by
  simp only [rConstrain]
  by_cases h1 : v < lo
  · simp [h1]
  · by_cases h2 : v > hi
    · simp [h1, h2]; exact h
    · simp [h1, h2]; exact Rat.not_lt.mp h1

theorem rConstrain_le (v lo hi : Rat) (h : lo ≤ hi) : rConstrain v lo hi ≤ hi := by
  simp only [rConstrain]
  by_cases h1 : v < lo
  · simp [h1]; exact h
  · by_cases h2 : v > hi
    · simp [h1, h2]
    · simp [h1, h2]; exact Rat.not_lt.mp h2

theorem rConstrain_in_range (v lo hi : Rat) (h : lo ≤ hi) :
    lo ≤ rConstrain v lo hi ∧ rConstrain v lo hi ≤ hi :=
  ⟨rConstrain_ge v lo hi h, rConstrain_le v lo hi h⟩

theorem rConstrain_id (v lo hi : Rat) (hlo : lo ≤ v) (hhi : v ≤ hi) :
    rConstrain v lo hi = v := by
  simp only [rConstrain]
  by_cases h1 : v < lo
  · exact absurd h1 (Rat.not_lt.mpr hlo)
  · by_cases h2 : v > hi
    · exact absurd h2 (Rat.not_lt.mpr hhi)
    · simp [h1, h2]

-- ============================================================
-- § 1  Types
-- ============================================================

/-- Parameters for the trapezoidal integrator. -/
structure ITParams where
  dt    : Rat   -- timestep (≥ 0 for forward integration)
  limit : Rat   -- symmetric saturation bound (≥ 0)

/-- State of the trapezoidal integrator. -/
structure ITState where
  y : Rat  -- current output (integrator state)
  u : Rat  -- previous input (used for trapezoidal rule)

-- ============================================================
-- § 2  Model
-- ============================================================

/-- One-step update of `BlockIntegralTrap`.

    Trapezoidal increment `(u_prev + input)/2 * dt` is added to `y`, then
    clamped to `[-limit, limit]`.  The previous input `u` is updated to
    `input` for the next step. -/
def itUpdate (p : ITParams) (s : ITState) (input : Rat) : ITState :=
  let trap := s.y + (s.u + input) / 2 * p.dt
  { y := rConstrain trap (-p.limit) p.limit,
    u := input }

/-- Iterate `itUpdate` over a list of inputs. -/
def itFold (p : ITParams) (s₀ : ITState) : List Rat → ITState
  | []      => s₀
  | x :: xs => itFold p (itUpdate p s₀ x) xs

-- Sanity checks
#eval (itUpdate { dt := 1, limit := 10 } { y := 0, u := 0 } 2).y    -- 1
#eval (itUpdate { dt := 1, limit := 10 } { y := 5, u := 3 } 7).y    -- 10
#eval (itUpdate { dt := 1, limit := 10 } { y := 9, u := 5 } 9).y    -- clamped to 10
#eval (itFold   { dt := 1, limit := 10 } { y := 0, u := 0 } [2, 2]).y  -- 3

-- ============================================================
-- § 3  Theorems
-- ============================================================

-- ─── 3.1  Output is bounded ────────────────────────────────

/-- The output `y` is always in `[-limit, limit]` (assuming `0 ≤ limit`). -/
theorem itUpdate_y_bounded (p : ITParams) (s : ITState) (input : Rat) (hlim : 0 ≤ p.limit) :
    -p.limit ≤ (itUpdate p s input).y ∧ (itUpdate p s input).y ≤ p.limit := by
  simp only [itUpdate]
  apply rConstrain_in_range
  have h1 : -p.limit ≤ 0 := by
    have := Rat.neg_le_neg hlim; rw [Rat.neg_zero] at this; exact this
  exact Rat.le_trans h1 hlim

/-- Lower bound alone. -/
theorem itUpdate_y_ge_neg_limit (p : ITParams) (s : ITState) (input : Rat) (hlim : 0 ≤ p.limit) :
    -p.limit ≤ (itUpdate p s input).y :=
  (itUpdate_y_bounded p s input hlim).1

/-- Upper bound alone. -/
theorem itUpdate_y_le_limit (p : ITParams) (s : ITState) (input : Rat) (hlim : 0 ≤ p.limit) :
    (itUpdate p s input).y ≤ p.limit :=
  (itUpdate_y_bounded p s input hlim).2

-- ─── 3.2  State update bookkeeping ─────────────────────────

/-- After an update, `u` is set to `input`. -/
theorem itUpdate_u_eq_input (p : ITParams) (s : ITState) (input : Rat) :
    (itUpdate p s input).u = input := by
  simp [itUpdate]

-- ─── 3.3  Trapezoidal formula (passthrough when in range) ──

/-- When the trapezoidal sum is within `[-limit, limit]`, output equals the
    exact trapezoidal accumulation (no clamping occurs). -/
theorem itUpdate_y_exact (p : ITParams) (s : ITState) (input : Rat)
    (hlo : -p.limit ≤ s.y + (s.u + input) / 2 * p.dt)
    (hhi : s.y + (s.u + input) / 2 * p.dt ≤ p.limit) :
    (itUpdate p s input).y = s.y + (s.u + input) / 2 * p.dt := by
  simp only [itUpdate]
  exact rConstrain_id _ _ _ hlo hhi

-- ─── 3.4  Increment formula ────────────────────────────────

/-- When the trapezoidal sum stays in range, the change in `y` equals
    the trapezoidal increment `(u_prev + input)/2 * dt`. -/
theorem itUpdate_increment_formula (p : ITParams) (s : ITState) (input : Rat)
    (hlo : -p.limit ≤ s.y + (s.u + input) / 2 * p.dt)
    (hhi : s.y + (s.u + input) / 2 * p.dt ≤ p.limit) :
    (itUpdate p s input).y - s.y = (s.u + input) / 2 * p.dt := by
  rw [itUpdate_y_exact p s input hlo hhi]
  rw [show s.y + (s.u + input) / 2 * p.dt - s.y =
        (s.u + input) / 2 * p.dt + s.y - s.y from by
    congr 1; exact Rat.add_comm _ _]
  exact Rat.add_sub_cancel

-- ─── 3.5  Zero-input / zero-state ──────────────────────────

/-- Zero state and zero input gives zero output (when `0 ≤ limit`). -/
theorem itUpdate_zero_state_zero_input (p : ITParams) (hlim : 0 ≤ p.limit) :
    (itUpdate p { y := 0, u := 0 } 0).y = 0 := by
  simp only [itUpdate]
  have htrap : (0 : Rat) + (0 + 0) / 2 * p.dt = 0 := by
    simp only [Rat.add_zero, Rat.zero_add]
    have h2 : (0 : Rat) / 2 = 0 := by native_decide
    rw [h2, Rat.zero_mul]
  rw [htrap]
  apply rConstrain_id
  · have h1 : -p.limit ≤ 0 := by
      have := Rat.neg_le_neg hlim; rw [Rat.neg_zero] at this; exact this
    exact h1
  · exact hlim

-- ─── 3.6  Iterated bound (inductive invariant) ─────────────

/-- If the initial state is in range, all fold outputs are in range. -/
theorem itFold_y_in_range (p : ITParams) (s₀ : ITState) (inputs : List Rat) (hlim : 0 ≤ p.limit)
    (hs : -p.limit ≤ s₀.y ∧ s₀.y ≤ p.limit) :
    -p.limit ≤ (itFold p s₀ inputs).y ∧ (itFold p s₀ inputs).y ≤ p.limit := by
  induction inputs generalizing s₀ with
  | nil => exact hs
  | cons x xs ih =>
    simp only [itFold]
    apply ih
    exact ⟨itUpdate_y_ge_neg_limit p s₀ x hlim,
           itUpdate_y_le_limit p s₀ x hlim⟩

-- ─── 3.7  Monotone trapezoidal sum (when dt ≥ 0) ───────────

/-- Larger input leads to a larger trapezoidal sum (when `dt ≥ 0`). -/
theorem itUpdate_trap_mono_input (p : ITParams) (s : ITState) (i1 i2 : Rat)
    (hdt : 0 ≤ p.dt) (hi : i1 ≤ i2) :
    s.y + (s.u + i1) / 2 * p.dt ≤ s.y + (s.u + i2) / 2 * p.dt := by
  apply Rat.add_le_add_left.mpr
  apply Rat.mul_le_mul_of_nonneg_right _ hdt
  simp only [Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right
    (Rat.add_le_add_left.mpr hi)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by native_decide)))

/-- When both trapezoidal sums stay in range, larger input gives larger output. -/
theorem itUpdate_y_mono_input_in_range (p : ITParams) (s : ITState) (i1 i2 : Rat)
    (hdt : 0 ≤ p.dt) (hi : i1 ≤ i2)
    (hlo1 : -p.limit ≤ s.y + (s.u + i1) / 2 * p.dt)
    (hhi2 : s.y + (s.u + i2) / 2 * p.dt ≤ p.limit) :
    (itUpdate p s i1).y ≤ (itUpdate p s i2).y := by
  have hmono := itUpdate_trap_mono_input p s i1 i2 hdt hi
  have hhi1 : s.y + (s.u + i1) / 2 * p.dt ≤ p.limit :=
    Rat.le_trans hmono hhi2
  have hlo2 : -p.limit ≤ s.y + (s.u + i2) / 2 * p.dt :=
    Rat.le_trans hlo1 hmono
  rw [itUpdate_y_exact p s i1 hlo1 hhi1, itUpdate_y_exact p s i2 hlo2 hhi2]
  exact hmono

-- ─── 3.8  Positive saturation ──────────────────────────────

/-- When the raw accumulation exceeds the limit, output is clamped to `limit`. -/
theorem itUpdate_saturated_pos (p : ITParams) (s : ITState) (input : Rat)
    (hlim : 0 <= p.limit)
    (hsat : s.y + (s.u + input) / 2 * p.dt > p.limit) :
    (itUpdate p s input).y = p.limit := by
  simp only [itUpdate, rConstrain]
  have h_neg_lim : -p.limit <= 0 := by
    have := Rat.neg_le_neg hlim; rw [Rat.neg_zero] at this; exact this
  have h_neg_le_v : -p.limit <= s.y + (s.u + input) / 2 * p.dt :=
    Rat.le_trans h_neg_lim (Rat.le_trans hlim (Rat.le_of_lt hsat))
  simp [Rat.not_lt.mpr h_neg_le_v, hsat]

-- ─── 3.9  Negative saturation ──────────────────────────────

/-- When the raw accumulation is below negative limit, output is clamped to `-limit`. -/
theorem itUpdate_saturated_neg (p : ITParams) (s : ITState) (input : Rat)
    (hsat : s.y + (s.u + input) / 2 * p.dt < -p.limit) :
    (itUpdate p s input).y = -p.limit := by
  simp only [itUpdate, rConstrain, hsat, if_true]

-- ─── 3.10  Concrete examples ───────────────────────────────

-- dt=1, limit=10, zero initial state, two steps with input=2: y → 1 → 3
example : (itFold { dt := 1, limit := 10 } { y := 0, u := 0 } [2, 2]).y = 3 := by
  native_decide

-- dt=2, limit=5, saturates at first step: 4 + (3+5)/2*2 = 4+8 = 12 → clamped to 5
example : (itUpdate { dt := 2, limit := 5 } { y := 4, u := 3 } 5).y = 5 := by
  native_decide

-- Zero state, zero input, zero output
example : (itUpdate { dt := 1, limit := 10 } { y := 0, u := 0 } 0).y = 0 := by
  native_decide

-- u is recorded
example : (itUpdate { dt := 1, limit := 10 } { y := 3, u := 1 } 7).u = 7 := by
  native_decide

-- Three-step bound: if init in range, all outputs in range
example : -5 <= (itFold { dt := 1, limit := 5 } { y := 0, u := 0 } [3, 4, 3]).y /\
              (itFold { dt := 1, limit := 5 } { y := 0, u := 0 } [3, 4, 3]).y <= 5 := by
  native_decide

-- Negative saturation: -10 + (-3 + (-8))/2 * 1 = -10 - 5.5 = -15.5 → clamped to -10
example : (itUpdate { dt := 1, limit := 10 } { y := -10, u := -3 } (-8)).y = -10 := by
  native_decide

end PX4.BlockIntegralTrap
