/-!
# PX4 `PID` Controller — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of PX4's generic PID controller:

- **C++ source**: `src/lib/pid/PID.cpp`, `src/lib/pid/PID.hpp`

## C++ Source (simplified)

```cpp
float PID::update(const float feedback, const float dt, const bool update_integral)
{
    const float error = _setpoint - feedback;
    const float output = (_gain_proportional * error) + _integral
                       + (_gain_derivative * updateDerivative(feedback, dt));
    if (update_integral) updateIntegral(error, dt);
    _last_feedback = feedback;
    return math::constrain(output, -_limit_output, _limit_output);
}

void PID::updateIntegral(float error, const float dt)
{
    const float integral_new = _integral + _gain_integral * error * dt;
    if (std::isfinite(integral_new))
        _integral = math::constrain(integral_new, -_limit_integral, _limit_integral);
}

float PID::updateDerivative(float feedback, const float dt)
{
    float feedback_change = 0.f;
    if ((dt > FLT_EPSILON) && std::isfinite(_last_feedback))
        feedback_change = (feedback - _last_feedback) / dt;
    return feedback_change;
}
```

## Model

We model over `Int` to obtain fully automated proofs via `omega`.
Floating-point behaviour (NaN/infinity, rounding, `FLT_EPSILON`) is abstracted:

- **`PIDState`**: holds integral accumulator and `Option Int` for `_last_feedback`
  (`none` = NaN initial state, first call).
- **`updateDerivative`**: returns 0 on first call (`none`) or when `dt ≤ 0`.
- **`updateIntegral`**: clamps the new integral to `[-limitI, limitI]`.
- **`pidOutput`**: clamps the raw output to `[-limitO, limitO]`.

## Approximations / Out of Scope

- Float NaN / ±∞ / rounding: not modelled; `Int` arithmetic is exact.
- `FLT_EPSILON` threshold on `dt`: modelled as strict `dt > 0`.
- `update_integral` flag: always `true` in the model.
- Mutable state: replaced by pure functional style.
-/

namespace PX4.PID

-- ============================================================
-- § 0  State and definitions
-- ============================================================

/-- PID controller state. `lastFeedback = none` encodes the first call (NaN in C++). -/
structure PIDState where
  integral : Int
  lastFeedback : Option Int
  deriving Repr

/-- Symmetric clamp: `val` clamped to `[-limit, limit]`.
    Models `math::constrain(val, -limit, limit)`. -/
private def clamp (val limit : Int) : Int :=
  if val < -limit then -limit
  else if val > limit then limit
  else val

/-- Model of `PID::updateDerivative`.
    First call (`none`): returns 0 (NaN guard). Positive dt: `(fb - prev) / dt`.
    Non-positive dt: returns 0. -/
def updateDerivative (fb dt : Int) : Option Int → Int
  | none      => 0
  | some prev => if dt > 0 then (fb - prev) / dt else 0

/-- Model of `PID::updateIntegral`: `clamp(integral + gainI * error * dt, limitI)`. -/
def updateIntegral (integral gainI error dt limitI : Int) : Int :=
  clamp (integral + gainI * error * dt) limitI

/-- Raw (unclamped) PID output. -/
def pidOutputRaw (sp fb dt gainP gainD : Int) (state : PIDState) : Int :=
  let error := sp - fb
  let deriv := updateDerivative fb dt state.lastFeedback
  gainP * error + state.integral + gainD * deriv

/-- Clamped PID output: `pidOutputRaw` clamped to `[-limitO, limitO]`. -/
def pidOutput (sp fb dt gainP gainD limitO : Int) (state : PIDState) : Int :=
  clamp (pidOutputRaw sp fb dt gainP gainD state) limitO

/-- Updated state after one PID step. -/
def pidNextState (sp fb dt gainI limitI : Int) (state : PIDState) : PIDState :=
  { integral := updateIntegral state.integral gainI (sp - fb) dt limitI,
    lastFeedback := some fb }

-- Sanity checks
#eval updateDerivative 5 1 none              -- 0 (first call)
#eval updateDerivative 5 1 (some 3)          -- 2
#eval updateIntegral 10 1 2 1 20             -- 12
#eval updateIntegral 19 1 5 1 20             -- 20 (clamped)
#eval updateIntegral (-19) 1 (-5) 1 20       -- -20 (clamped)

-- ============================================================
-- § 1  `clamp` — basic properties
-- ============================================================

/-- `clamp` output is always ≥ -limit when limit ≥ 0. -/
theorem clamp_ge_neg (val limit : Int) (h : 0 ≤ limit) : -limit ≤ clamp val limit := by
  simp only [clamp]
  by_cases h1 : val < -limit
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : val > limit
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- `clamp` output is always ≤ limit when limit ≥ 0. -/
theorem clamp_le (val limit : Int) (h : 0 ≤ limit) : clamp val limit ≤ limit := by
  simp only [clamp]
  by_cases h1 : val < -limit
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : val > limit
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- `clamp` output is within [-limit, limit] when limit ≥ 0. -/
theorem clamp_in_range (val limit : Int) (h : 0 ≤ limit) :
    -limit ≤ clamp val limit ∧ clamp val limit ≤ limit :=
  ⟨clamp_ge_neg val limit h, clamp_le val limit h⟩

/-- `clamp 0 limit = 0` when limit ≥ 0. -/
theorem clamp_zero (limit : Int) (h : 0 ≤ limit) : clamp 0 limit = 0 := by
  simp only [clamp]
  by_cases h1 : (0 : Int) < -limit
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : (0 : Int) > limit
    · rw [if_pos h2]; omega
    · rw [if_neg h2]

/-- `clamp` is the identity when `val` is already in range. -/
theorem clamp_of_mem (val limit : Int) (hlo : -limit ≤ val) (hhi : val ≤ limit) :
    clamp val limit = val := by
  simp only [clamp]
  by_cases h1 : val < -limit
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : val > limit
    · rw [if_pos h2]; omega
    · rw [if_neg h2]

/-- `clamp` to limit is idempotent when limit ≥ 0. -/
theorem clamp_idempotent (val limit : Int) (h : 0 ≤ limit) :
    clamp (clamp val limit) limit = clamp val limit :=
  clamp_of_mem _ _ (clamp_ge_neg val limit h) (clamp_le val limit h)

/-- `clamp` is monotone: larger input → larger (or equal) output (when limit ≥ 0). -/
theorem clamp_mono (val val' limit : Int) (hL : 0 ≤ limit) (h : val ≤ val') :
    clamp val limit ≤ clamp val' limit := by
  simp only [clamp]
  by_cases h1 : val < -limit
  · rw [if_pos h1]
    by_cases h3 : val' < -limit
    · rw [if_pos h3]; omega
    · rw [if_neg h3]
      by_cases h4 : val' > limit
      · rw [if_pos h4]; omega
      · rw [if_neg h4]; omega
  · rw [if_neg h1]
    by_cases h2 : val > limit
    · rw [if_pos h2]
      by_cases h3 : val' < -limit
      · rw [if_pos h3]; omega
      · rw [if_neg h3]
        by_cases h4 : val' > limit
        · rw [if_pos h4]; omega
        · rw [if_neg h4]; omega
    · rw [if_neg h2]
      by_cases h3 : val' < -limit
      · rw [if_pos h3]; omega
      · rw [if_neg h3]
        by_cases h4 : val' > limit
        · rw [if_pos h4]; omega
        · rw [if_neg h4]; omega

-- ============================================================
-- § 2  `updateIntegral` — clamping and anti-windup properties
-- ============================================================

/-- `updateIntegral` output is always ≥ -limitI when limitI ≥ 0. -/
theorem updateIntegral_ge_neg (integral gainI error dt limitI : Int) (h : 0 ≤ limitI) :
    -limitI ≤ updateIntegral integral gainI error dt limitI :=
  clamp_ge_neg _ limitI h

/-- `updateIntegral` output is always ≤ limitI when limitI ≥ 0. -/
theorem updateIntegral_le (integral gainI error dt limitI : Int) (h : 0 ≤ limitI) :
    updateIntegral integral gainI error dt limitI ≤ limitI :=
  clamp_le _ limitI h

/-- `updateIntegral` output is within [-limitI, limitI] when limitI ≥ 0.

    **Key anti-windup invariant**: the integral is always bounded by `limitI`,
    preventing integrator windup regardless of accumulated error. -/
theorem updateIntegral_in_range (integral gainI error dt limitI : Int) (h : 0 ≤ limitI) :
    -limitI ≤ updateIntegral integral gainI error dt limitI ∧
    updateIntegral integral gainI error dt limitI ≤ limitI :=
  ⟨updateIntegral_ge_neg _ _ _ _ _ h, updateIntegral_le _ _ _ _ _ h⟩

/-- When error = 0 and integral is in range, `updateIntegral` leaves the integral unchanged. -/
theorem updateIntegral_zero_error (integral gainI dt limitI : Int)
    (hlo : -limitI ≤ integral) (hhi : integral ≤ limitI) :
    updateIntegral integral gainI 0 dt limitI = integral := by
  unfold updateIntegral
  have heq : integral + gainI * 0 * dt = integral := by simp
  rw [heq]
  exact clamp_of_mem integral limitI hlo hhi

/-- `updateIntegral` is monotone in error:
    larger error (with gainI ≥ 0, dt ≥ 0) → larger (or equal) integral.

    This captures the accumulation direction: persistent positive error drives
    the integral upward. -/
theorem updateIntegral_mono_error (integral gainI error error' dt limitI : Int)
    (hL : 0 ≤ limitI) (hgI : 0 ≤ gainI) (hdt : 0 ≤ dt) (herr : error ≤ error') :
    updateIntegral integral gainI error dt limitI ≤
    updateIntegral integral gainI error' dt limitI := by
  unfold updateIntegral
  apply clamp_mono _ _ _ hL
  have h1 : gainI * error ≤ gainI * error' := Int.mul_le_mul_of_nonneg_left herr hgI
  have h2 : gainI * error * dt ≤ gainI * error' * dt := Int.mul_le_mul_of_nonneg_right h1 hdt
  omega

-- ============================================================
-- § 3  `updateDerivative` — basic properties
-- ============================================================

/-- On the first call (`lastFeedback = none`), the derivative is 0.
    Models the C++ `isfinite` guard: NaN → zero derivative. -/
theorem updateDerivative_first_call (fb dt : Int) :
    updateDerivative fb dt none = 0 := rfl

/-- When feedback is constant and dt > 0, the derivative is 0 (steady state). -/
theorem updateDerivative_steady_state (fb dt : Int) (hdt : 0 < dt) :
    updateDerivative fb dt (some fb) = 0 := by
  simp only [updateDerivative, show dt > 0 from hdt, ite_true, Int.sub_self, Int.zero_ediv]

/-- When dt ≤ 0, the derivative is always 0 regardless of history. -/
theorem updateDerivative_nonpos_dt (fb dt prev : Int) (hdt : dt ≤ 0) :
    updateDerivative fb dt (some prev) = 0 := by
  simp only [updateDerivative, show ¬dt > 0 from by omega, ite_false]

-- ============================================================
-- § 4  `pidOutput` — clamping properties
-- ============================================================

/-- `pidOutput` is always ≥ -limitO when limitO ≥ 0.

    **Key safety invariant**: regardless of gains, error, or integral state,
    the actuator command is always lower-bounded. -/
theorem pidOutput_ge_neg (sp fb dt gainP gainD limitO : Int)
    (state : PIDState) (h : 0 ≤ limitO) :
    -limitO ≤ pidOutput sp fb dt gainP gainD limitO state :=
  clamp_ge_neg _ limitO h

/-- `pidOutput` is always ≤ limitO when limitO ≥ 0. -/
theorem pidOutput_le (sp fb dt gainP gainD limitO : Int)
    (state : PIDState) (h : 0 ≤ limitO) :
    pidOutput sp fb dt gainP gainD limitO state ≤ limitO :=
  clamp_le _ limitO h

/-- `pidOutput` is within [-limitO, limitO] when limitO ≥ 0.

    **Output safety invariant**: the PID output is bounded, preventing
    actuator over-command regardless of controller state or input. -/
theorem pidOutput_in_range (sp fb dt gainP gainD limitO : Int)
    (state : PIDState) (h : 0 ≤ limitO) :
    -limitO ≤ pidOutput sp fb dt gainP gainD limitO state ∧
    pidOutput sp fb dt gainP gainD limitO state ≤ limitO :=
  ⟨pidOutput_ge_neg _ _ _ _ _ _ _ h, pidOutput_le _ _ _ _ _ _ _ h⟩

-- ============================================================
-- § 5  Equilibrium theorems
-- ============================================================

/-- **Steady-state zero output**: when setpoint = feedback, integral = 0,
    and feedback has been constant (last = some fb), the output is 0.

    Fundamental equilibrium property: at steady state with zero error and
    no accumulated integral, the controller demands no action. -/
theorem pidOutput_zero_steady_state (fb dt gainP gainD limitO : Int)
    (h : 0 ≤ limitO) :
    pidOutput fb fb dt gainP gainD limitO { integral := 0, lastFeedback := some fb } = 0 := by
  have hderiv : updateDerivative fb dt (some fb) = 0 := by
    by_cases hdt : dt > 0
    · exact updateDerivative_steady_state fb dt hdt
    · exact updateDerivative_nonpos_dt fb dt fb (by omega)
  simp only [pidOutput, pidOutputRaw, hderiv]
  simp [clamp_zero limitO h]

/-- **First-call zero output at equilibrium**: when setpoint = feedback, integral = 0,
    and this is the first call, the output is 0. -/
theorem pidOutput_zero_first_call (fb dt gainP gainD limitO : Int)
    (h : 0 ≤ limitO) :
    pidOutput fb fb dt gainP gainD limitO { integral := 0, lastFeedback := none } = 0 := by
  simp only [pidOutput, pidOutputRaw, updateDerivative_first_call]
  simp [clamp_zero limitO h]

-- ============================================================
-- § 6  Monotonicity of `pidOutput`
-- ============================================================

/-- `pidOutput` is monotone in the setpoint (when gainP ≥ 0, limitO ≥ 0):
    larger setpoint → larger (or equal) output. -/
theorem pidOutput_mono_sp (sp sp' fb dt gainP gainD limitO : Int)
    (state : PIDState)
    (hL : 0 ≤ limitO) (hgP : 0 ≤ gainP) (hsp : sp ≤ sp') :
    pidOutput sp  fb dt gainP gainD limitO state ≤
    pidOutput sp' fb dt gainP gainD limitO state := by
  unfold pidOutput
  apply clamp_mono _ _ _ hL
  simp only [pidOutputRaw]
  have h := Int.mul_le_mul_of_nonneg_left (show sp - fb ≤ sp' - fb from by omega) hgP
  omega

/-- `pidOutput` is monotone in the integral state (when limitO ≥ 0):
    larger stored integral → larger (or equal) output. -/
theorem pidOutput_mono_integral (sp fb dt gainP gainD limitO : Int)
    (state state' : PIDState)
    (hL : 0 ≤ limitO)
    (hi : state.integral ≤ state'.integral)
    (hlast : state.lastFeedback = state'.lastFeedback) :
    pidOutput sp fb dt gainP gainD limitO state ≤
    pidOutput sp fb dt gainP gainD limitO state' := by
  unfold pidOutput
  apply clamp_mono _ _ _ hL
  simp only [pidOutputRaw, hlast]
  omega

-- ============================================================
-- § 7  Multi-step iteration and convergence
-- ============================================================

/-- `pidIntegralIterate gainI error dt limitI state n` applies `updateIntegral`
    with a fixed `error` exactly `n` times, returning the integral after `n` steps. -/
def pidIntegralIterate (gainI error dt limitI : Int) : Int → Nat → Int
  | acc, 0     => acc
  | acc, n + 1 => pidIntegralIterate gainI error dt limitI
                    (updateIntegral acc gainI error dt limitI) n

/-- **Iterated integral stays in range**: after any number of steps the integral
    remains in `[-limitI, limitI]`, provided the initial value is in range and
    `limitI ≥ 0`. -/
theorem pidIntegralIterate_in_range (gainI error dt limitI : Int) (h : 0 ≤ limitI)
    (init : Int) (hinit_lo : -limitI ≤ init) (hinit_hi : init ≤ limitI)
    (n : Nat) :
    -limitI ≤ pidIntegralIterate gainI error dt limitI init n ∧
    pidIntegralIterate gainI error dt limitI init n ≤ limitI := by
  induction n generalizing init with
  | zero => simp [pidIntegralIterate]; exact ⟨hinit_lo, hinit_hi⟩
  | succ k ih =>
    simp only [pidIntegralIterate]
    apply ih
    · exact updateIntegral_ge_neg init gainI error dt limitI h
    · exact updateIntegral_le   init gainI error dt limitI h

/-- **Zero-error iteration is identity**: when `error = 0`, `updateIntegral`
    is the identity on any integral value (independent of `gainI`, `dt`). -/
theorem updateIntegral_zero_error_id (integral gainI dt limitI : Int)
    (_h : 0 ≤ limitI) (hlo : -limitI ≤ integral) (hhi : integral ≤ limitI) :
    updateIntegral integral gainI 0 dt limitI = integral := by
  simp only [updateIntegral, Int.mul_zero, Int.zero_mul, Int.add_zero]
  exact clamp_of_mem integral limitI hlo hhi

/-- **Iterated zero-error integral is constant**: applying `updateIntegral` any
    number of times with `error = 0` leaves the integral unchanged. -/
theorem pidIntegralIterate_zero_error (gainI dt limitI : Int) (h : 0 ≤ limitI)
    (init : Int) (hinit_lo : -limitI ≤ init) (hinit_hi : init ≤ limitI)
    (n : Nat) :
    pidIntegralIterate gainI 0 dt limitI init n = init := by
  induction n generalizing init with
  | zero => simp [pidIntegralIterate]
  | succ k ih =>
    simp only [pidIntegralIterate]
    rw [updateIntegral_zero_error_id init gainI dt limitI h hinit_lo hinit_hi]
    exact ih init hinit_lo hinit_hi

/-- **Multi-step state iteration**: `pidStateIterate` applies one complete PID step
    (integral update + feedback update) `n` times with constant setpoint and
    feedback. -/
def pidStateIterate (sp fb dt gainI limitI : Int) : PIDState → Nat → PIDState
  | s, 0     => s
  | s, n + 1 => pidStateIterate sp fb dt gainI limitI (pidNextState sp fb dt gainI limitI s) n

/-- The integral component of `pidStateIterate` stays in `[-limitI, limitI]`. -/
theorem pidStateIterate_integral_in_range (sp fb dt gainI limitI : Int) (h : 0 ≤ limitI)
    (s : PIDState) (hlo : -limitI ≤ s.integral) (hhi : s.integral ≤ limitI)
    (n : Nat) :
    -limitI ≤ (pidStateIterate sp fb dt gainI limitI s n).integral ∧
    (pidStateIterate sp fb dt gainI limitI s n).integral ≤ limitI := by
  induction n generalizing s with
  | zero => simp [pidStateIterate]; exact ⟨hlo, hhi⟩
  | succ k ih =>
    simp only [pidStateIterate]
    apply ih
    · exact updateIntegral_ge_neg s.integral gainI (sp - fb) dt limitI h
    · exact updateIntegral_le   s.integral gainI (sp - fb) dt limitI h

/-- **Multi-step state at equilibrium is stable**: starting from the equilibrium
    state `{integral:=0, lastFeedback:=some fb}` with `sp = fb`, iterating any
    number of steps returns the same equilibrium state. -/
theorem pidStateIterate_equilibrium_stable
    (fb dt gainI limitI : Int) (hI : 0 ≤ limitI)
    (n : Nat) :
    pidStateIterate fb fb dt gainI limitI
      { integral := 0, lastFeedback := some fb } n =
      { integral := 0, lastFeedback := some fb } := by
  -- Key lemma: one step from equilibrium returns to equilibrium
  have one_step : pidNextState fb fb dt gainI limitI
      { integral := 0, lastFeedback := some fb } =
      { integral := 0, lastFeedback := some fb } := by
    simp only [pidNextState, updateIntegral, Int.sub_self, Int.mul_zero, Int.zero_mul,
               Int.add_zero]
    simp only [clamp_zero limitI hI]
  induction n with
  | zero => simp [pidStateIterate]
  | succ k ih =>
    simp only [pidStateIterate]
    rw [one_step]
    exact ih

/-- **Zero output at equilibrium after multiple steps**: when `sp = fb` and the
    initial integral is 0 (steady state), every step of `pidOutput` returns 0. -/
theorem pidOutput_zero_equilibrium_iterate
    (fb dt gainP gainD limitO gainI limitI : Int)
    (hL : 0 ≤ limitO) (hI : 0 ≤ limitI)
    (n : Nat) :
    let s₀ : PIDState := { integral := 0, lastFeedback := some fb }
    let sₙ := pidStateIterate fb fb dt gainI limitI s₀ n
    pidOutput fb fb dt gainP gainD limitO sₙ = 0 := by
  simp only
  rw [pidStateIterate_equilibrium_stable fb dt gainI limitI hI n]
  exact pidOutput_zero_steady_state fb dt gainP gainD limitO hL

end PX4.PID
