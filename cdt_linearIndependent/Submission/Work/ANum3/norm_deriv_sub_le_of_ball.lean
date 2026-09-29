import Mathlib

namespace Work.ANum3

theorem norm_deriv_sub_le_of_ball {f : ℂ → ℂ} {c y : ℂ} {ρ C : ℝ} (hρ : 0 ≤ ρ)
    (hf' : ∀ z : ℂ, ‖z - c‖ ≤ ρ → DifferentiableAt ℂ (deriv f) z)
    (h2 : ∀ z : ℂ, ‖z - c‖ ≤ ρ → ‖deriv (deriv f) z‖ ≤ C)
    (hy : ‖y - c‖ ≤ ρ) :
    ‖deriv f y - deriv f c‖ ≤ C * ‖y - c‖ := by
  have hconv : Convex ℝ (Metric.closedBall c ρ) := convex_closedBall c ρ
  have hc : c ∈ Metric.closedBall c ρ := Metric.mem_closedBall_self hρ
  have hy' : y ∈ Metric.closedBall c ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hf' z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz))
    (fun z hz => h2 z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz))
    hconv hc hy'

end Work.ANum3
