import Mathlib
import Submission.Work.Cert.rot_aux

namespace Work.Cert

open Complex Submission.CDTPlan Work.CNum

/-- `rot (2927/25000)`, correctly rounded at scale `S = 2^40·10^8`.
Template: copy `rot0_bound` at the end of `Submission/Work/Cert/rot_aux.lean` (import it) and
substitute `rot1r = 81518292988615043513`, `rot1i = 73783643881070330236`, `t = 2927/25000`;
the glue lemma `Work.Cert.rot_bound_aux` and the `π`-bound helpers are in the same file. -/
theorem rot1_bound : ‖Work.Cert.cx Work.Cert.rot1r Work.Cert.rot1i - Submission.CDTPlan.rot (2927 / 25000)‖ ≤ 2 / (Work.Cert.S : ℝ) := by
  have h4 : 2 * (3.14159265358979323847 : ℝ) * (2927 / 25000) ≤ Real.pi / 4 := by
    have h1 : 2 * (3.14159265358979323847 : ℝ) * (2927 / 25000)
        ≤ (3.14159265358979323846 : ℝ) / 4 := by norm_num
    have h2 : (3.14159265358979323846 : ℝ) / 4 ≤ Real.pi / 4 := by linarith [Real.pi_gt_d20]
    linarith
  exact rot_bound_aux (2927 / 25000) rot1r rot1i (by norm_num) h4
    (by rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        norm_num [S, rot1r])
    (by rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        norm_num [S, rot1r])
    (by rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        norm_num [S, rot1i])
    (by rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        norm_num [S, rot1i])

end Work.Cert
