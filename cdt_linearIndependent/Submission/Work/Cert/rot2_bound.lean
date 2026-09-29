import Mathlib
import Submission.Work.Cert.rot_aux

namespace Work.Cert

open Complex Submission.CDTPlan Work.CNum

/-- `rot (453/12500)`, correctly rounded at scale `S = 2^40·10^8`.
Template: copy `rot0_bound` at the end of `Submission/Work/Cert/rot_aux.lean` (import it) and
substitute `rot2r = 107113056366341060795`, `rot2i = 24820381786091335080`, `t = 453/12500`. -/
theorem rot2_bound : ‖Work.Cert.cx Work.Cert.rot2r Work.Cert.rot2i - Submission.CDTPlan.rot (453 / 12500)‖ ≤ 2 / (Work.Cert.S : ℝ) := by
  have h4 : 2 * (3.14159265358979323847 : ℝ) * (453 / 12500) ≤ Real.pi / 4 := by
    have h1 : 2 * (3.14159265358979323847 : ℝ) * (453 / 12500)
        ≤ (3.14159265358979323846 : ℝ) / 4 := by norm_num
    have h2 : (3.14159265358979323846 : ℝ) / 4 ≤ Real.pi / 4 := by linarith [Real.pi_gt_d20]
    linarith
  refine rot_bound_aux (453 / 12500) rot2r rot2i (by norm_num) h4 ?_ ?_ ?_ ?_
  · rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot2r]
  · rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot2r]
  · rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot2i]
  · rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot2i]

end Work.Cert
