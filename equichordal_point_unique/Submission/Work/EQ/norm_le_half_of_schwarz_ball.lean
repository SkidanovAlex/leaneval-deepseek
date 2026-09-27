import Mathlib

namespace Work.EQ

/-- Consequence of the Schwarz lemma: if `Y` is analytic on the ball of radius `R`
about `0`, fixes `0`, and maps that ball strictly inside itself, then `Y` maps the
ball of radius `R / 2` into the ball of radius `R / 2`. -/
theorem norm_le_half_of_schwarz_ball {Y : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hYan : AnalyticOnNhd ℂ Y (Metric.ball (0 : ℂ) R))
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ R → ‖Y w‖ < R) (hY0 : Y 0 = 0) {w : ℂ} (hw : ‖w‖ ≤ R / 2) :
    ‖Y w‖ ≤ R / 2 := by
  have hdiff : DifferentiableOn ℂ Y (Metric.ball (0 : ℂ) R) := hYan.differentiableOn
  have hmaps : Set.MapsTo Y (Metric.ball (0 : ℂ) R) (Metric.closedBall (Y 0) R) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, hY0, sub_zero]
    exact le_of_lt (hstrict z (le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz)))
  have hw' : w ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have h1 := Complex.dist_le_dist_of_mapsTo_ball hdiff hmaps hw'
  rw [dist_eq_norm, hY0, sub_zero, dist_eq_norm, sub_zero] at h1
  linarith

end Work.EQ
