import Mathlib
import Submission.Work.Pert.scale_cauchy

namespace Work.Pert.LiftExp

theorem lipschitz_u_on_ball {u : ℂ → ℂ} {rr : ℝ} (hrr : 0 < rr)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2) :
    ∀ z ∈ Metric.ball (0 : ℂ) (rr / 2), ∀ w ∈ Metric.ball (0 : ℂ) (rr / 2),
      ‖u z - u w‖ ≤ (8 / rr) * ‖z - w‖ := by
  intro z hz w hw
  -- work on the closed half-ball, which is convex and contains both points
  set s : Set ℂ := Metric.closedBall (0 : ℂ) (rr / 2) with hs
  have hzs : z ∈ s := Metric.ball_subset_closedBall hz
  have hws : w ∈ s := Metric.ball_subset_closedBall hw
  -- `u` is differentiable at every point of `s` (which is inside the ball of radius `rr`)
  have hdiff : ∀ x ∈ s, DifferentiableAt ℂ u x := by
    intro x hx
    rw [hs, Metric.mem_closedBall, dist_zero_right] at hx
    have hxρ : x ∈ Metric.ball (0 : ℂ) rr := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact hu.differentiableAt (Metric.isOpen_ball.mem_nhds hxρ)
  -- and the Cauchy estimate gives `‖u'‖ ≤ 8 / rr` on `s`
  have hbound : ∀ x ∈ s, ‖deriv u x‖ ≤ 8 / rr := by
    intro x hx
    rw [hs, Metric.mem_closedBall, dist_zero_right] at hx
    exact Work.Pert.deriv_bound hrr le_rfl hu hu2 x hx
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_closedBall (0 : ℂ) (rr / 2)) hzs hws
  -- `hmvt : ‖u w - u z‖ ≤ (8 / rr) * ‖w - z‖`
  rwa [← norm_sub_rev (u z) (u w), ← norm_sub_rev z w] at hmvt

end Work.Pert.LiftExp
