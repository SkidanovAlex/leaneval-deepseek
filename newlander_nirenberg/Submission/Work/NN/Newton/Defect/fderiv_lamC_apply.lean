import Mathlib
import Submission.Work.NN.Newton.DefectDefs

namespace Work.NN.Newton.Defect

theorem fderiv_lamC_apply {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (w : Work.NN.Core.Cn n) {z : Work.NN.Core.Cn n} (hA : DifferentiableAt ℝ A z)
    (X : Work.NN.Core.Cn n) :
    fderiv ℝ (fun z' => Work.NN.Newton.lamC l (A z' w)) z X
      = Work.NN.Newton.lamC l ((fderiv ℝ A z X) w) := by
  -- Write the integrand as the composition of the continuous linear map
  -- `L T = λ(T w)` (built from `λ` and the evaluation-at-`w` map) with `A`.
  set L : (Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) →L[ℝ] ℂ :=
    (Work.NN.Newton.lamC l).comp (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w) with hL
  have hfun : (fun z' : Work.NN.Core.Cn n => Work.NN.Newton.lamC l (A z' w)) = ⇑L ∘ A := by
    funext z'
    simp only [Function.comp_apply, hL, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, Work.NN.Newton.lamC_apply]
  rw [hfun]
  -- Chain rule for the composition `L ∘ A`; `L` is linear hence differentiable everywhere.
  have hg : DifferentiableAt ℝ (⇑L) (A z) := L.hasFDerivAt.differentiableAt
  rw [fderiv_comp (x := z) hg hA]
  -- The derivative of the linear map `L` is `L` itself; unfold the definition of `L`.
  rw [ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hL, ContinuousLinearMap.apply_apply,
    Work.NN.Newton.lamC_apply]

end Work.NN.Newton.Defect
