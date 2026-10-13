/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The time reversal `timFlip`

For the shifted Agmon passage `ShiftedFlatAux` the `b ≥ 0` branch uses the backward
particular solution `ShiftFT.Gc`; the `b ≤ 0` branch is handled here by the time reversal
`t ↦ -t`, which turns the operator `L_b = ∂_t - b` into `-L_{-b}`.  Since all the slots of
the statement are *squares*, the reversal transports both the hypotheses and the conclusion.

This file only fixes the definition (and its elementary algebraic properties); the pointwise
and integral transfer lemmas live in `Submission/Work/FTS/EllSol/SpecAux/FlipPlumb.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The time reversal `(t,θ) ↦ u (-t) θ`. -/
def timFlip (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => u (-t) θ

@[simp] theorem timFlip_apply (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    timFlip u t θ = u (-t) θ := rfl

@[simp] theorem timFlip_neg (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    timFlip u (-t) θ = u t θ := by simp [timFlip]

theorem timFlip_involutive (u : ℝ → ℝ → ℝ) : timFlip (timFlip u) = u := by
  funext t θ
  simp [timFlip]

/-- The set of the strip is invariant under the time reversal. -/
theorem timFlip_strip :
    (fun p : ℝ × ℝ => (-p.1, p.2)) '' ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      = (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨trivial, hq.2⟩
  · intro hp
    exact ⟨(-p.1, p.2), ⟨trivial, hp.2⟩, by simp⟩

/-- `Function.uncurry (timFlip u)` is the time reversal of `Function.uncurry u`. -/
theorem uncurry_timFlip (u : ℝ → ℝ → ℝ) :
    Function.uncurry (timFlip u) = fun p : ℝ × ℝ => Function.uncurry u (-p.1, p.2) := by
  funext p
  simp [Function.uncurry, timFlip]

/-- The reversal of the uncurrying is the composition with the (smooth) map
`(t,θ) ↦ (-t,θ)`. -/
theorem uncurry_timFlip_eq_comp (u : ℝ → ℝ → ℝ) :
    Function.uncurry (timFlip u) = Function.uncurry u ∘ fun p : ℝ × ℝ => (-p.1, p.2) := by
  funext p
  simp [Function.uncurry, timFlip]

end

end Work.FTS.EllSol.SpecAux
