import Mathlib

set_option linter.unusedVariables false

namespace Work.Pert

/-- The mean value inequality for a complex-differentiable function on the disc of radius `ρ`:
if `‖deriv F‖` is bounded by `D` on that disc, then `F` is `D`-Lipschitz there. -/
theorem hF_lipschitz_on_ball {F : ℂ → ℂ} {ρ D : ℝ} (hρ : 0 < ρ)
    (hFd : DifferentiableOn ℂ F (Metric.ball 0 ρ))
    (hFl : ∀ z ∈ Metric.ball 0 ρ, ‖deriv F z‖ ≤ D)
    {a b : ℂ} (ha : a ∈ Metric.ball 0 ρ) (hb : b ∈ Metric.ball 0 ρ) :
    ‖F a - F b‖ ≤ D * ‖a - b‖ := by
  -- the ball is open, so differentiability on it gives differentiability at each of its points
  have hdiff : ∀ z ∈ Metric.ball 0 ρ, DifferentiableAt ℂ F z :=
    fun z hz => (hFd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  -- apply the complex mean value inequality on the convex ball, in the orientation `b → a`
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hFl (convex_ball 0 ρ) hb ha

end Work.Pert
