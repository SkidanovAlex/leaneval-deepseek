import Mathlib
import Submission.Work.ZeroFreeTables.TentRowAux

namespace Work.ZeroFreeTables

/-- Row certificates 7-11 of `Work.ZeroFreeTables.tentRows`.  Recipe (constants `B = n/10^12` and
the one-line proof template): see the table in `Submission/Work/ZeroFreeTables/TentRowAux.lean`,
mathlib module `Submission.Work.ZeroFreeTables.TentRowAux`; here `n = 1297546274791, 1316333210077,
1337601553827, 1343411803365, 1369805487729` in that order. -/
theorem TentRowsB3 :
    Work.ZeroFreeTables.TentRowCert ((23/20 : ℝ), (42475267 : ℝ)/10^9, (3624 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((23/20 : ℝ), (36113688 : ℝ)/10^9, (3824 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((23/20 : ℝ), (30064306 : ℝ)/10^9, (4047 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((11/10 : ℝ), (24506098 : ℝ)/10^9, (4294 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((11/10 : ℝ), (19540814 : ℝ)/10^9, (4577 : ℝ)/1000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine TentRowCert_of_poly (23/20 : ℝ) ((42475267 : ℝ)/10^9) ((3624 : ℝ)/1000)
      ((1297546274791 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (23/20 : ℝ) ((36113688 : ℝ)/10^9) ((3824 : ℝ)/1000)
      ((1316333210077 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (23/20 : ℝ) ((30064306 : ℝ)/10^9) ((4047 : ℝ)/1000)
      ((1337601553827 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (11/10 : ℝ) ((24506098 : ℝ)/10^9) ((4294 : ℝ)/1000)
      ((1343411803365 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (11/10 : ℝ) ((19540814 : ℝ)/10^9) ((4577 : ℝ)/1000)
      ((1369805487729 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

end Work.ZeroFreeTables
