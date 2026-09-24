import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Commons.Analysis.Complex

/-- The contour integral of the logarithmic derivative `f'/f` of a function `f` that is analytic
and zero-free on the closed ball `Metric.closedBall c R` vanishes along the circle `C(c, R)`.

This is the Cauchy-Goursat theorem applied to `logDeriv f = f'/f`, which is holomorphic on the
closed ball: both `f` and `deriv f` are analytic at every point of `Metric.closedBall c R`, and
`f` does not vanish there, so `f'/f` is continuous on the closed ball and differentiable on its
interior. -/
theorem circleIntegral_logDeriv_eq_zero_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ Metric.closedBall c R, AnalyticAt ℂ f z)
    (hne : ∀ z ∈ Metric.closedBall c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
  · -- `logDeriv f = f'/f` is continuous on the closed ball.
    intro z hz
    have hzan : AnalyticAt ℂ f z := hf z hz
    have hzne : f z ≠ 0 := hne z hz
    have h3 : ContinuousAt (fun w => deriv f w / f w) z :=
      (hzan.deriv.continuousAt).div hzan.continuousAt hzne
    change ContinuousWithinAt (fun w => deriv f w / f w) (Metric.closedBall c R) z
    exact h3.continuousWithinAt
  · -- `logDeriv f = f'/f` is complex differentiable on the open ball.
    intro z hz
    have hz' : z ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hz.1
    have hzan : AnalyticAt ℂ f z := hf z hz'
    have hzne : f z ≠ 0 := hne z hz'
    have h3 : DifferentiableAt ℂ (fun w => deriv f w / f w) z :=
      hzan.deriv.differentiableAt.div hzan.differentiableAt hzne
    change DifferentiableAt ℂ (fun w => deriv f w / f w) z
    exact h3

end Commons.Analysis.Complex