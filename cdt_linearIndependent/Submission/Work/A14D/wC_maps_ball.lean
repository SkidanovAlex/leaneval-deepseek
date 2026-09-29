import Mathlib
import Submission.Work.A14.defs

namespace Work.A14D

/-- The Möbius map `w(z) = z/(z−1)` sends the ball `ball (1/9) δ` (`δ ≤ 1/20`) into the ball
`ball (−1/8) (1/10)`, since `w(z) + 1/8 = 9(z − 1/9) / (8(z − 1))`. -/
theorem wC_maps_ball {δ : ℝ} (hδ20 : δ ≤ 1 / 20) {z : ℂ}
    (hz : z ∈ Metric.ball ninth δ) : wC z ∈ Metric.ball (-(1 / 8) : ℂ) (1 / 10) := by
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  have hδ : ‖z - ninth‖ < 1 / 20 := lt_of_lt_of_le hz hδ20
  -- `z - 1 = -8/9 + (z - 1/9)`, so `‖z - 1‖ ≥ 8/9 - ‖z - 1/9‖ > 8/9 - 1/20 = 151/180`.
  have hsplit : z - 1 = -((8 : ℂ) / 9) + (z - ninth) := by
    simp only [ninth]; ring
  have hB : (151 : ℝ) / 180 < ‖z - 1‖ := by
    rw [hsplit]
    have h1 : ‖((8 : ℂ) / 9)‖ = (8 / 9 : ℝ) := by
      rw [show ((8 : ℂ) / 9) = ((8 / 9 : ℝ) : ℂ) by norm_num]
      exact Complex.norm_of_nonneg (by norm_num)
    have h2 : ‖((8 : ℂ) / 9)‖ - ‖z - ninth‖ ≤
        ‖-((8 : ℂ) / 9) + (z - ninth)‖ := by
      have h3 := norm_sub_norm_le (-((8 : ℂ) / 9)) (-(z - ninth))
      rw [norm_neg, norm_neg,
          show -((8 : ℂ) / 9) - (-(z - ninth))
              = -((8 : ℂ) / 9) + (z - ninth) by ring] at h3
      exact h3
    rw [h1] at h2
    linarith
  -- `w(z) + 1/8 = 9(z − 1/9) / (8(z − 1))`.
  have hzw : wC z - (-(1 / 8)) = 9 * (z - ninth) / (8 * (z - 1)) := by
    have hz1 : z - 1 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hB
      norm_num at hB
    rw [wC, ninth]
    field_simp
    ring
  rw [hzw, norm_div, norm_mul, norm_mul,
      show (9 : ℂ) = ((9 : ℝ) : ℂ) by norm_num, Complex.norm_of_nonneg (by norm_num),
      show (8 : ℂ) = ((8 : ℝ) : ℂ) by norm_num, Complex.norm_of_nonneg (by norm_num)]
  -- Reduce to the numerical inequality `9‖z − 1/9‖ < (1/10)·8‖z − 1‖`.
  have hpos : (0 : ℝ) < 8 * ‖z - 1‖ := by
    have := norm_nonneg (z - 1); linarith [hB]
  rw [div_lt_iff₀ hpos]
  nlinarith [hδ, hB, norm_nonneg (z - ninth)]

end Work.A14D
