import Mathlib
import Submission.Work.Cert.rot_aux

namespace Work.Cert

open Complex Submission.CDTPlan Work.CNum

/-- `rot (-1971/25000)`, correctly rounded at scale `S = 2^40·10^8`.
Reduce to the positive angle with `Work.Cert.norm_cx_rot_neg` (in `rot_aux`):
`Work.Cert.norm_cx_rot_neg rot3r rot3i (1971/25000)` gives
`‖cx rot3r rot3i - rot (-1971/25000)‖ = ‖cx rot3r (-rot3i) - rot (1971/25000)‖`, and the
right-hand side is the template `rot0_bound` with `x = rot3r = 96734442863377519137`,
`y = -rot3i = 52265722611078878142`, `t = 1971/25000`. -/
theorem rot3_bound : ‖Work.Cert.cx Work.Cert.rot3r Work.Cert.rot3i - Submission.CDTPlan.rot (-1971 / 25000)‖ ≤ 2 / (Work.Cert.S : ℝ) := by
  have hneg : (-1971 : ℝ) / 25000 = -(1971 / 25000) := by norm_num
  rw [hneg, norm_cx_rot_neg rot3r rot3i (1971 / 25000)]
  have h4 : 2 * (3.14159265358979323847 : ℝ) * (1971 / 25000) ≤ Real.pi / 4 := by
    have h1 : 2 * (3.14159265358979323847 : ℝ) * (1971 / 25000)
        ≤ (3.14159265358979323846 : ℝ) / 4 := by norm_num
    have h2 : (3.14159265358979323846 : ℝ) / 4 ≤ Real.pi / 4 := by
      linarith [Real.pi_gt_d20]
    linarith
  refine rot_bound_aux (1971 / 25000) rot3r (-rot3i) (by norm_num) h4 ?_ ?_ ?_ ?_
  · rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot3r]
  · rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot3r]
  · rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot3i]
  · rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot3i]

end Work.Cert
