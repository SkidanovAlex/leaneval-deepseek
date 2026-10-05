import Mathlib
import Submission.Work.RPB.B1a.HalfBallRegion

namespace Work.RPB.B1a

theorem shearRegion_snd_lt (P Q : ℝ → ℝ) {r x y : ℝ} (hr : 0 < r)
    (hnocap : ∀ x, |x| ≤ 2 * r → |Q x| < r → P x + Real.sqrt (r ^ 2 - (Q x) ^ 2) ≤ r)
    (h : (x, y) ∈ Work.RPB.B1a.shearRegion P Q r) : y < r := by
  rw [mem_shearRegion] at h
  obtain ⟨hy, hineq, hball⟩ := h
  -- membership in the ball gives `|x| < 2 * r`
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def] at hball
  have hxr : |x| < 2 * r := lt_of_le_of_lt (le_max_left _ _) hball
  -- the first-coordinate term cannot be too large
  have hQsq : (Q x) ^ 2 < r ^ 2 := by nlinarith [sq_nonneg (y - P x)]
  have hQr : |Q x| < r := by
    have h1 := sq_lt_sq.mp hQsq
    rwa [abs_of_pos hr] at h1
  have hcap := hnocap x (le_of_lt hxr) hQr
  have hpos : 0 ≤ r ^ 2 - (Q x) ^ 2 := by linarith
  have hsq : (y - P x) ^ 2 < (Real.sqrt (r ^ 2 - (Q x) ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hpos]; linarith
  have hlt : |y - P x| < Real.sqrt (r ^ 2 - (Q x) ^ 2) := by
    have h1 : |y - P x| < |Real.sqrt (r ^ 2 - (Q x) ^ 2)| := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h1
  have : y - P x ≤ |y - P x| := le_abs_self _
  linarith

end Work.RPB.B1a
