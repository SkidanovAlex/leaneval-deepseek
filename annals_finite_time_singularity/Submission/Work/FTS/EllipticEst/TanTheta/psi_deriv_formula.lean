import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TanTheta.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta

/-- For `θ ∈ (0, π/2)` the derivative of `ψ = u / cos` is
`ψ' θ = (u' θ cos θ + u θ sin θ) / cos θ ^ 2`.

Route: the quotient rule `HasDerivAt.div` applied to the differentiability of `u` at `θ`
(available since `Set.Ioo (-1) (Real.pi / 2 + 1)` is an open neighbourhood of `θ`) and
`Real.hasDerivAt_cos`, then `HasDerivAt.deriv` to turn it into a `deriv` statement. -/
theorem psi_deriv_formula (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ
      = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
  have hmem : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hd : HasDerivAt u (deriv u θ) θ :=
    (hu.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds hmem)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hdiv : HasDerivAt (u / Real.cos)
      ((deriv u θ * Real.cos θ - u θ * (-Real.sin θ)) / Real.cos θ ^ 2) θ :=
    hd.div (Real.hasDerivAt_cos θ) hcos
  change deriv (u / Real.cos) θ
      = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2
  rw [hdiv.deriv]
  ring

end Work.FTS.EllipticEst.TanTheta
