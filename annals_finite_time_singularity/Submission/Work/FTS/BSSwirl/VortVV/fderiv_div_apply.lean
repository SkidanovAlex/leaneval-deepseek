import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.Trace
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.BSSwirl.contDiff_div_and_support

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl.VortVV

theorem fderiv_div_apply (Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (x v : Work.FTS.BSSwirl.R3) :
    fderiv ℝ (FiniteTimeSingularity.div Ψ) x v
      = (fderiv ℝ (fderiv ℝ Ψ) x v).trace ℝ Work.FTS.BSSwirl.R3 := by
  -- `div Ψ = divTrCLM ∘ fderiv ℝ Ψ`, definitionally (trace as a continuous linear
  -- functional of the derivative).
  have hdiv : FiniteTimeSingularity.div Ψ
      = fun y => Work.FTS.BSSwirl.divTrCLM (fderiv ℝ Ψ y) := by
    funext y
    rfl
  rw [hdiv]
  -- `fderiv ℝ Ψ` is `C¹` because `Ψ` is `C²`; hence it is differentiable at `x` with
  -- derivative `fderiv ℝ (fderiv ℝ Ψ) x`, and the chain rule applies to `divTrCLM`.
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
    (((hΨ 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hder : HasFDerivAt (fun y => Work.FTS.BSSwirl.divTrCLM (fderiv ℝ Ψ y))
      (Work.FTS.BSSwirl.divTrCLM.comp (fderiv ℝ (fderiv ℝ Ψ) x)) x :=
    Work.FTS.BSSwirl.divTrCLM.hasFDerivAt.comp x hd.hasFDerivAt
  rw [hder.fderiv, ContinuousLinearMap.comp_apply]
  exact Work.FTS.BSSwirl.divTrCLM_apply _

end Work.FTS.BSSwirl.VortVV
