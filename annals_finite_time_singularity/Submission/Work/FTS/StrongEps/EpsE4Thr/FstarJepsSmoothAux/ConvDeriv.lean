import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- The convolution `s' ↦ ∫ p, κ p * g (s' - p)` is differentiable at `s` with derivative
`∫ p, deriv κ p * g (s - p)`, for `κ` of class `C¹` with compact support and `g` merely locally
integrable: this is the one-variable case of `HasCompactSupport.hasDerivAt_convolution_left`
(the convolution with the bilinear operator `ContinuousLinearMap.mul ℝ ℝ`, whose defining
integral is exactly `∫ p, κ p * g (s' - p)`, since this is definitionally
`MeasureTheory.convolution_mul`). -/
theorem ConvDeriv {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hκc : HasCompactSupport κ)
    {g : ℝ → ℝ} (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) (s : ℝ) :
    HasDerivAt (fun s' => ∫ p, κ p * g (s' - p))
      (∫ p, deriv κ p * g (s - p)) s := by
  have h : HasDerivAt (fun s' => ∫ p, κ p * g (s' - p)) (∫ p, deriv κ p * g (s - p)) s :=
    hκc.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hκ hg s
  exact h

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
