import Mathlib
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero

namespace Commons.Analysis.Complex

/-- The contour integral of the logarithmic derivative `g'/g` of a function `g` that is analytic
and zero-free on the ball `Metric.ball 0 ρ₁` vanishes along any circle `C(0, ρ)` with `ρ < ρ₁`.

This is the ball-analytic version of `circleIntegral_logDeriv_eq_zero_of_ne_zero`: the closed
ball of radius `ρ` is contained in the ball of radius `ρ₁`, so `g` is analytic and nonvanishing
on it and the Cauchy–Goursat argument applies. -/
theorem circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_ball {g : ℂ → ℂ} {ρ ρ₁ : ℝ}
    (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0:ℂ) ρ₁))
    (hgne : ∀ z ∈ Metric.ball (0:ℂ) ρ₁, g z ≠ 0) :
    circleIntegral (fun z => logDeriv g z) 0 ρ = 0 := by
  have hsub : Metric.closedBall (0:ℂ) ρ ⊆ Metric.ball (0:ℂ) ρ₁ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  exact circleIntegral_logDeriv_eq_zero_of_ne_zero hρ (fun z hz => hg z (hsub hz))
    (fun z hz => hgne z (hsub hz))

end Commons.Analysis.Complex
