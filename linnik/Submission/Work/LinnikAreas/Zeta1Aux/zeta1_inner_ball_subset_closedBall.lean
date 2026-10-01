import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

theorem zeta1_inner_ball_subset_closedBall {t : ℝ} (ht : 5 ≤ |t|) :
    Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10) ⊆
      Metric.closedBall (0 : ℂ) (|t| + 6) := by
  intro z hz
  simp only [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
  have h1 : ‖z‖ ≤
      ‖z - ((2 : ℂ) + Complex.I * (t : ℂ))‖ + ‖((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
    calc ‖z‖ = ‖(z - ((2 : ℂ) + Complex.I * (t : ℂ))) +
          ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ |t| + 2 := by
    calc ‖((2 : ℂ) + Complex.I * (t : ℂ))‖
        ≤ ‖(2 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
      _ = |t| + 2 := by ring
  simp only [sub_zero]
  linarith

end Work.LinnikAreas.Zeta1Aux
