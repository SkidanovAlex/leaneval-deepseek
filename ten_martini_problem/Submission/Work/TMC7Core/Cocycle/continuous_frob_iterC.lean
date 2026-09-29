import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle

/-!
# Continuity of `x ↦ ‖A_n(x)‖_F`

The Frobenius norm `frob` is a composition of the (continuous) entry maps, the norm on `ℂ`
and `Real.sqrt`; hence, composed with the continuous transfer iterate `x ↦ iterC α lam E n x`,
it is continuous.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMC7Core.Cocycle

/-- `frob` is continuous on `2 × 2` complex matrices, being a composition of the continuous
entry maps, the norm on `ℂ` and `Real.sqrt`. -/
theorem continuous_frob : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) =
      fun A => Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := rfl
  rw [h]
  fun_prop

theorem continuous_frob_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) :
    Continuous (fun x : ℝ => frob (iterC α lam E n x)) := by
  have h : (fun x : ℝ => frob (iterC α lam E n x)) =
      (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) ∘ (fun x : ℝ => iterC α lam E n x) := rfl
  rw [h]
  exact continuous_frob.comp (continuous_iterC α lam E n)

end Work.TMC7Core.Cocycle

end
