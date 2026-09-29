import Mathlib
import Submission.Work.Cert.rot_aux

namespace Work.Cert

/-- `rot (1/4096)`, correctly rounded at scale `S = 2^40·10^8`.
Template: copy `rot0_bound` at the end of `Submission/Work/Cert/rot_aux.lean` (import it) and
substitute `WR = 109951033414746560990`, `WI = 168662905159809435`, `t = 1/4096`. -/
theorem rotW_bound : ‖Work.Cert.cx Work.Cert.WR Work.Cert.WI - Submission.CDTPlan.rot (1 / 4096)‖ ≤ 2 / (Work.Cert.S : ℝ) := by
  open Work.CNum in
  have h4 : 2 * (3.14159265358979323847 : ℝ) * (1 / 4096) ≤ Real.pi / 4 := by
    have h1 : 2 * (3.14159265358979323847 : ℝ) * (1 / 4096)
        ≤ (3.14159265358979323846 : ℝ) / 4 := by norm_num
    have h2 : (3.14159265358979323846 : ℝ) / 4 ≤ Real.pi / 4 := by
      linarith [Real.pi_gt_d20]
    linarith
  refine rot_bound_aux (1 / 4096) WR WI (by norm_num) h4 ?_ ?_ ?_ ?_
  · rw [Work.CNum.cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WR]
  · rw [Work.CNum.cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WR]
  · rw [Work.CNum.sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WI]
  · rw [Work.CNum.sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WI]

end Work.Cert
