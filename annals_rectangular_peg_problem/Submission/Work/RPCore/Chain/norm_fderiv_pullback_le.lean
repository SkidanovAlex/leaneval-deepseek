import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPCore.Chain

theorem norm_fderiv_pullback_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Work.RPV.PS → ℝ) (L : E →L[ℝ] Work.RPV.PS) (M : ℝ) (hf : Differentiable ℝ f)
    (hbd : ∀ x, ‖fderiv ℝ f x‖ ≤ M) :
    ∀ z, ‖fderiv ℝ (fun z => f (L z)) z‖ ≤ M * ‖L‖ := by
  intro z
  have hcomp : fderiv ℝ (fun z => f (L z)) z = (fderiv ℝ f (L z)).comp L :=
    (((hf (L z)).hasFDerivAt).comp z L.hasFDerivAt).fderiv
  rw [hcomp]
  calc ‖(fderiv ℝ f (L z)).comp L‖
      ≤ ‖fderiv ℝ f (L z)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * ‖L‖ := mul_le_mul_of_nonneg_right (hbd (L z)) (norm_nonneg L)

end Work.RPCore.Chain
