import Mathlib
import Submission.Work.A14D.LC_A_defs

namespace Work.A14D

/-- On the disc of radius `39/100` around the origin, the deck involution `w(z) = z/(z−1)` is
strictly contracting towards `0`: `‖w z‖ < 1`.

Since `‖z − 1‖ ≥ ‖1‖ − ‖z‖ = 1 − ‖z‖ ≥ 1 − 39/100 = 61/100` and `‖z‖ ≤ 39/100 < 61/100`, we get
`‖w z‖ = ‖z‖ / ‖z − 1‖ ≤ (39/100)/(61/100) < 1`. -/
theorem wC_norm_lt_one {z : ℂ} (hz : ‖z‖ ≤ (39 : ℝ) / 100) : ‖Work.A14D.wC z‖ < 1 := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  rw [wC, norm_div]
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  rw [div_lt_one hpos]
  have hle : (61 : ℝ) / 100 ≤ ‖z - 1‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, norm_sub_rev] at h
    have h2 : |(1 : ℝ) - ‖z‖| = 1 - ‖z‖ := abs_of_nonneg (by linarith)
    rw [h2] at h
    linarith
  linarith

end Work.A14D
