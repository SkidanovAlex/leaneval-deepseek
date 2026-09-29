import Mathlib
import Submission.Work.C17.lc_defs

namespace Work.C17I

/-- For `z` in the ball of radius `1/20` about `p₀ = 1/4 + i/5`, both `‖z/(z-1)‖ < 8/9` and
`‖z‖ ≤ 39/100`. -/
theorem ball_p0C_bounds {z : ℂ} (hz : z ∈ Metric.ball Work.C17.p0C (1 / 20)) :
    ‖z / (z - 1)‖ < 8 / 9 ∧ ‖z‖ ≤ 39 / 100 := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  -- `hz : ‖z - p0C‖ < 1/20`
  have hnum : ‖z‖ < 38 / 100 := by
    have h1 : ‖z‖ = ‖(z - Work.C17.p0C) + Work.C17.p0C‖ := by rw [sub_add_cancel]
    rw [h1]
    have h2 : ‖(z - Work.C17.p0C) + Work.C17.p0C‖ ≤ ‖z - Work.C17.p0C‖ + ‖Work.C17.p0C‖ :=
      norm_add_le _ _
    have h3 : ‖Work.C17.p0C‖ ≤ (33:ℝ)/100 := Work.C17.norm_p0C_le
    linarith
  have hgt : (29:ℝ)/40 < ‖Work.C17.p0C - 1‖ := by
    have hsq : ‖Work.C17.p0C - 1‖ ^ 2 = (241:ℝ)/400 := Work.C17.norm_p0C_sub_one_sq
    have h2 : ((29:ℝ)/40)^2 < ‖Work.C17.p0C - 1‖^2 := by rw [hsq]; norm_num
    have h3 : |(29:ℝ)/40| < |‖Work.C17.p0C - 1‖| := sq_lt_sq.mp h2
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (29:ℝ)/40),
        abs_of_nonneg (norm_nonneg (Work.C17.p0C - 1))] at h3
    exact h3
  have hden : ‖z - 1‖ > 27/40 := by
    have htri : ‖Work.C17.p0C - 1‖ ≤ ‖Work.C17.p0C - z‖ + ‖z - 1‖ := by
      have : Work.C17.p0C - 1 = (Work.C17.p0C - z) + (z - 1) := by ring
      rw [this]
      exact norm_add_le _ _
    have h1 : ‖Work.C17.p0C - z‖ = ‖z - Work.C17.p0C‖ := norm_sub_rev _ _
    rw [h1] at htri
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_div, div_lt_iff₀ (by linarith : (0:ℝ) < ‖z - 1‖)]
    nlinarith [hnum, hden]
  · linarith

end Work.C17I
