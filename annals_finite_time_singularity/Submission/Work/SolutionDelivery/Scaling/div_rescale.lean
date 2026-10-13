import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

/-- **The divergence of a rescaled field.**  For `g = fun y ↦ λ • F (λ • y)` the chain rule gives
`Dg(x) = λ • (DF(λx) ∘ (λ • id)) = λ² • DF(λx)`, and `trace : End →ₗ[ℝ] ℝ` is linear, so
`div g x = λ² · div F (λx)`.  The two `fderiv` identities used are hypothesis-free in Mathlib
(`fderiv_comp_smul`, `fderiv_const_smul_field`), so no differentiability of `F` is needed —
in particular the statement also holds for `λ = 0`. -/
theorem div_rescale {lam : ℝ} {F : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (hlam : lam ≠ 0) (x : Work.SolutionDelivery.R3) :
    FiniteTimeSingularity.div (fun y => lam • F (lam • y)) x
      = lam ^ 2 * FiniteTimeSingularity.div F (lam • x) := by
  -- The derivative of `λ • F (λ • ·)`: chain rule for `f ∘ (λ • ·)`, then scalar pull-out.
  have h1 : fderiv ℝ (fun y : Work.SolutionDelivery.R3 => lam • F (lam • y)) x
      = lam • fderiv ℝ (fun z : Work.SolutionDelivery.R3 => lam • F z) (lam • x) :=
    fderiv_comp_smul (f := fun z : Work.SolutionDelivery.R3 => lam • F z) (x := x) lam
  have h2 : fderiv ℝ (fun z : Work.SolutionDelivery.R3 => lam • F z) (lam • x)
      = lam • fderiv ℝ F (lam • x) :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := F) lam) (lam • x)
  have h3 : fderiv ℝ (fun y : Work.SolutionDelivery.R3 => lam • F (lam • y)) x
      = lam ^ 2 • fderiv ℝ F (lam • x) := by rw [h1, h2, smul_smul, sq]
  simp only [FiniteTimeSingularity.div, h3, ContinuousLinearMap.toLinearMap_smul, map_smul,
    smul_eq_mul]

end Work.SolutionDelivery.Scaling
