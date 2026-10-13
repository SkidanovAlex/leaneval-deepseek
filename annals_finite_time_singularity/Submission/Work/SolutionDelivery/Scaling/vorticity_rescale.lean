import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

/-- **Rescaling of the vorticity.**  Under the Euler scaling `u ↦ (x ↦ λ • u (λ • x))`, the
vorticity `∇ × u` transforms as `(∇ × (λ • F ∘ (λ • ·))) x = λ² • (∇ × F) (λ • x)`.

This is the spatial part of the classical scaling `u'(x,t) = λ u(λx, λ²t)`: the curl is a single
spatial derivative, so it picks up exactly one power of `λ`, and each component of the curl is
evaluated at the rescaled point `λx`.

The proof is the chain rule, in the unconditional (`fderiv`) form that avoids any differentiability
hypothesis on `F`:
`fderiv ℝ (λ • F ∘ (λ • ·)) x = λ • fderiv ℝ (λ • F) (λ • x) = λ² • fderiv ℝ F (λ • x)`
(`fderiv_comp_smul`, `fderiv_const_smul_field`), followed by the bilinearity of the cross product,
the linearity of `WithLp.toLp` and the linearity of finite sums. -/
theorem vorticity_rescale {lam : ℝ} {F : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (hlam : lam ≠ 0) (x : Work.SolutionDelivery.R3) :
    FiniteTimeSingularity.vorticity (fun y => lam • F (lam • y)) x
      = lam ^ 2 • FiniteTimeSingularity.vorticity F (lam • x) := by
  -- The derivative of the rescaled field: `fderiv (λ • F ∘ (λ • ·)) x = λ² • fderiv F (λ • x)`.
  have hderiv : fderiv ℝ (fun y => lam • F (lam • y)) x = lam ^ 2 • fderiv ℝ F (lam • x) := by
    rw [show (fun y => lam • F (lam • y)) = (fun y => (fun z => lam • F z) (lam • y)) from rfl,
      fderiv_comp_smul (𝕜 := ℝ) (f := fun z => lam • F z) lam]
    rw [show fderiv ℝ (fun z => lam • F z) (lam • x) = lam • fderiv ℝ F (lam • x) from
      congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := F) lam) (lam • x), smul_smul, sq]
  -- Unfold the vorticity on both sides and use the derivative formula inside the sum.
  simp only [FiniteTimeSingularity.vorticity]
  rw [hderiv]
  -- Push the scalar `λ²` out of the cross products and out of the sum / `WithLp.toLp`.
  simp only [smul_apply, WithLp.ofLp_smul, map_smul]
  conv_lhs => rw [← Finset.smul_sum]
  rw [WithLp.toLp_smul]

end Work.SolutionDelivery.Scaling
