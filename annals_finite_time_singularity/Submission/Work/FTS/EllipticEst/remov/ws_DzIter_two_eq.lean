import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.WProductRule
import Submission.Work.FTS.EllipticEst.remov.wsDzSplits

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- The elementary product-rule splitting `D_z² Ψ = D_z Ψ + z² ∂_z² Ψ`: the operator
first component of `wsDzSplits`, restated with `D_z Ψ` written as the definitional
unfolding `D_z^1 Ψ`. -/
theorem ws_DzIter_two_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ :=
  (wsDzSplits hΨ hz hθ).1

end Work.FTS.EllipticEst.remov
