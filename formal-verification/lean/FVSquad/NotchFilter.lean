/-!
# NotchFilter — Formal Specification and Proofs

🔬 *Lean Squad automated formal verification.*

**Target**: `math::NotchFilter<T>::applyInternal` — Direct Form I IIR notch filter
**C++ source**: `src/lib/mathlib/math/filter/NotchFilter.hpp`

## Model

We model the filter over `Int` (integers). The filter state holds four delay
elements (x1, x2, y1, y2) and five coefficients (b0, b1, b2, a1, a2).

The core recurrence mirrors `applyInternal` exactly:

```cpp
T output = b0*sample + b1*x1 + b2*x2 - a1*y1 - a2*y2;
x2 = x1; x1 = sample; y2 = y1; y1 = output;
```

Using `Int` and `omega` gives fully automated proofs.

## What is modelled
- Pure `applyInternal` recurrence (one scalar step)
- Iterated application (`nfIter`)
- Bypass/identity mode (b0=1, b1=b2=a1=a2=0)
- DC steady-state propagation
- Zero-input zero-state response
- Two-step output explicit formula
- Superposition (linearity in sample)
- State-update register correctness

## What is NOT modelled
- Floating-point rounding (we use `Int`)
- The `setParameters` coefficient computation (transcendental math)
- Vector specialisation (T = matrix)
- Initialization logic (`_initialized` flag, `reset(sample)`)
- `isFinite` / NaN guards

All proofs use `omega` or `simp` only — no sorry.
-/

namespace PX4.NotchFilter

/-! ## State -/

structure NFState where
  x1 : Int   -- _delay_element_1   (previous input)
  x2 : Int   -- _delay_element_2   (input two steps ago)
  y1 : Int   -- _delay_element_output_1 (previous output)
  y2 : Int   -- _delay_element_output_2 (output two steps ago)
  deriving Repr, DecidableEq

structure NFCoeffs where
  b0 : Int
  b1 : Int
  b2 : Int
  a1 : Int
  a2 : Int
  deriving Repr, DecidableEq

/-! ## Core recurrence: applyInternal -/

/-- One step of Direct Form I. Mirrors `NotchFilter<T>::applyInternal` exactly.
    Returns (output, next_state). -/
def nfApply (c : NFCoeffs) (s : NFState) (sample : Int) : Int × NFState :=
  let output := c.b0 * sample + c.b1 * s.x1 + c.b2 * s.x2
              - c.a1 * s.y1  - c.a2 * s.y2
  (output, { x1 := sample, x2 := s.x1, y1 := output, y2 := s.y1 })

/-- Output of one step. -/
def nfOut (c : NFCoeffs) (s : NFState) (sample : Int) : Int :=
  (nfApply c s sample).1

/-- Next state after one step. -/
def nfNext (c : NFCoeffs) (s : NFState) (sample : Int) : NFState :=
  (nfApply c s sample).2

/-- Iterate over a list of samples. Returns output list and final state. -/
def nfIter (c : NFCoeffs) (s : NFState) : List Int → List Int × NFState
  | []      => ([], s)
  | x :: xs =>
      let (y, s') := nfApply c s x
      let (ys, sn) := nfIter c s' xs
      (y :: ys, sn)

/-! ## Definitional / unfolding lemmas -/

theorem nfOut_def (c : NFCoeffs) (s : NFState) (sample : Int) :
    nfOut c s sample =
      c.b0 * sample + c.b1 * s.x1 + c.b2 * s.x2 - c.a1 * s.y1 - c.a2 * s.y2 := rfl

/-- After one step, the new x1 register holds the current input (shift register). -/
theorem nfNext_x1 (c : NFCoeffs) (s : NFState) (sample : Int) :
    (nfNext c s sample).x1 = sample := rfl

/-- After one step, the new x2 register holds the old x1 (shift register). -/
theorem nfNext_x2 (c : NFCoeffs) (s : NFState) (sample : Int) :
    (nfNext c s sample).x2 = s.x1 := rfl

/-- After one step, the new y1 register holds the computed output. -/
theorem nfNext_y1 (c : NFCoeffs) (s : NFState) (sample : Int) :
    (nfNext c s sample).y1 = nfOut c s sample := rfl

/-- After one step, the new y2 register holds the old y1. -/
theorem nfNext_y2 (c : NFCoeffs) (s : NFState) (sample : Int) :
    (nfNext c s sample).y2 = s.y1 := rfl

/-! ## Bypass / identity mode -/

/-- PX4 default bypass coefficients: b0=1, b1=b2=a1=a2=0. -/
def bypassCoeffs : NFCoeffs := { b0 := 1, b1 := 0, b2 := 0, a1 := 0, a2 := 0 }

/-- In bypass mode, output equals the input sample (regardless of state). -/
theorem nfOut_bypass (s : NFState) (sample : Int) :
    nfOut bypassCoeffs s sample = sample := by
  simp [nfOut_def, bypassCoeffs]

/-- In bypass mode, iterating over any list returns the same list unchanged. -/
theorem nfIter_bypass (s : NFState) (xs : List Int) :
    (nfIter bypassCoeffs s xs).1 = xs := by
  induction xs generalizing s with
  | nil => simp [nfIter]
  | cons x rest ih =>
    simp only [nfIter, nfApply, bypassCoeffs]
    have hout : (1 : Int) * x + 0 * s.x1 + 0 * s.x2 - 0 * s.y1 - 0 * s.y2 = x := by omega
    rw [hout]
    congr 1
    exact ih _

/-! ## Zero-input, zero-state response -/

/-- With zero input and all-zero state, the output is zero. -/
theorem nfOut_zero_state (c : NFCoeffs) :
    nfOut c { x1 := 0, x2 := 0, y1 := 0, y2 := 0 } 0 = 0 := by
  simp [nfOut_def]

/-- With zero input and zero state, n steps produce all-zero output. -/
theorem nfIter_zero (c : NFCoeffs) (n : Nat) :
    nfIter c { x1 := 0, x2 := 0, y1 := 0, y2 := 0 } (List.replicate n 0) =
      (List.replicate n 0, { x1 := 0, x2 := 0, y1 := 0, y2 := 0 }) := by
  induction n with
  | zero => simp [nfIter]
  | succ k ih =>
    simp only [List.replicate, nfIter, nfApply]
    have hout : c.b0 * (0 : Int) + c.b1 * 0 + c.b2 * 0 - c.a1 * 0 - c.a2 * 0 = 0 := by omega
    rw [hout, ih]

/-! ## DC / steady-state condition -/

/-- IIR DC unity gain condition: b0+b1+b2 = 1+a1+a2.
    Under this condition with all state = dc and input = dc, the output is dc. -/
theorem nfOut_dc_steady (c : NFCoeffs) (dc : Int)
    (hdc : c.b0 + c.b1 + c.b2 = 1 + c.a1 + c.a2) :
    nfOut c { x1 := dc, x2 := dc, y1 := dc, y2 := dc } dc = dc := by
  simp [nfOut_def]
  have factor : c.b0 * dc + c.b1 * dc + c.b2 * dc - c.a1 * dc - c.a2 * dc =
                (c.b0 + c.b1 + c.b2 - c.a1 - c.a2) * dc := by
    simp [Int.add_mul, Int.sub_mul]
  have key : c.b0 + c.b1 + c.b2 - c.a1 - c.a2 = 1 := by omega
  rw [factor, key, Int.one_mul]

/-- Under DC-unity, n steps of constant input `dc` from DC-steady state
    produce n copies of `dc` and leave the state unchanged. -/
theorem nfIter_dc_steady (c : NFCoeffs) (dc : Int)
    (hdc : c.b0 + c.b1 + c.b2 = 1 + c.a1 + c.a2) (n : Nat) :
    let s : NFState := { x1 := dc, x2 := dc, y1 := dc, y2 := dc }
    nfIter c s (List.replicate n dc) =
      (List.replicate n dc, { x1 := dc, x2 := dc, y1 := dc, y2 := dc }) := by
  intro s
  induction n with
  | zero => simp [nfIter, s]
  | succ k ih =>
    simp only [List.replicate, nfIter]
    have hout : c.b0 * dc + c.b1 * dc + c.b2 * dc - c.a1 * dc - c.a2 * dc = dc := by
      have factor : c.b0 * dc + c.b1 * dc + c.b2 * dc - c.a1 * dc - c.a2 * dc =
                    (c.b0 + c.b1 + c.b2 - c.a1 - c.a2) * dc := by
        simp [Int.add_mul, Int.sub_mul]
      have key : c.b0 + c.b1 + c.b2 - c.a1 - c.a2 = 1 := by omega
      rw [factor, key, Int.one_mul]
    simp only [nfApply, s, hout, ih]

/-! ## Superposition: linearity in the current sample -/

/-- The output is additive in the sample:
    nfOut(u+v) = nfOut(u) + b0*v.
    This captures the superposition principle for Direct Form I. -/
theorem nfOut_add_sample (c : NFCoeffs) (s : NFState) (u v : Int) :
    nfOut c s (u + v) = nfOut c s u + c.b0 * v := by
  simp only [nfOut_def, Int.mul_add]
  omega

/-! ## Two-step explicit formula -/

/-- The output at step 2 (with inputs `u` then `v`) in terms of the initial state.
    This is the unrolled Direct Form I recurrence for two steps. -/
theorem nfOut_step2 (c : NFCoeffs) (s : NFState) (u v : Int) :
    nfOut c (nfNext c s u) v =
      c.b0 * v + c.b1 * u + c.b2 * s.x1
      - c.a1 * (c.b0 * u + c.b1 * s.x1 + c.b2 * s.x2 - c.a1 * s.y1 - c.a2 * s.y2)
      - c.a2 * s.y1 := by
  simp [nfOut_def, nfNext, nfApply]

/-! ## Output list length -/

/-- Iterating over a list of length n produces exactly n output values. -/
theorem nfIter_length (c : NFCoeffs) (s : NFState) (xs : List Int) :
    (nfIter c s xs).1.length = xs.length := by
  induction xs generalizing s with
  | nil => simp [nfIter]
  | cons x rest ih =>
    simp [nfIter]
    exact ih _

/-! ## Concrete examples (verified by computation) -/

/-- Bypass: output = input regardless of state. -/
example : nfOut bypassCoeffs { x1 := 1, x2 := 2, y1 := 3, y2 := 4 } 7 = 7 := by decide

/-- Pure b0=2 gain with zero state: output = 2 * sample. -/
example : nfOut { b0 := 2, b1 := 0, b2 := 0, a1 := 0, a2 := 0 }
               { x1 := 0, x2 := 0, y1 := 0, y2 := 0 } 5 = 10 := by decide

/-- One step with non-trivial coefficients and state. -/
example : nfOut { b0 := 1, b1 := 1, b2 := 0, a1 := 0, a2 := 0 }
               { x1 := 3, x2 := 0, y1 := 0, y2 := 0 } 7 = 10 := by decide

/-- DC steady state: b0+b1=1+a1 (b2=a2=0), dc=5 → output=5. -/
example : nfOut { b0 := 1, b1 := 0, b2 := 0, a1 := 0, a2 := 0 }
               { x1 := 5, x2 := 5, y1 := 5, y2 := 5 } 5 = 5 := by decide

/-- Bypass iteration: [1,2,3] → [1,2,3]. -/
example : (nfIter bypassCoeffs { x1 := 0, x2 := 0, y1 := 0, y2 := 0 } [1, 2, 3]).1
         = [1, 2, 3] := by decide

/-- Zero input zero state: 3 steps → [0,0,0]. -/
example : (nfIter { b0 := 3, b1 := 2, b2 := 1, a1 := 1, a2 := 1 }
                  { x1 := 0, x2 := 0, y1 := 0, y2 := 0 } [0, 0, 0]).1
         = [0, 0, 0] := by decide

/-- Length: 5 inputs → 5 outputs. -/
example : (nfIter bypassCoeffs { x1 := 0, x2 := 0, y1 := 0, y2 := 0 }
                [10, 20, 30, 40, 50]).1.length = 5 := by decide

end PX4.NotchFilter
