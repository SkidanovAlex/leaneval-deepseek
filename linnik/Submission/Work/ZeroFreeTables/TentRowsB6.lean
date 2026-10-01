import Mathlib
import Submission.Work.ZeroFreeTables.TentRowAux

namespace Work.ZeroFreeTables

/-- Row certificates 22-26 of `Work.ZeroFreeTables.tentRows`.  Recipe (constants `B = n/10^12` and
the one-line proof template): see the table in `Submission/Work/ZeroFreeTables/TentRowAux.lean`,
mathlib module `Submission.Work.ZeroFreeTables.TentRowAux`; here `n = 1929237794918, 2036153522860,
2156663820206, 2291742625486, 2442293361194` in that order. -/
theorem TentRowsB6 :
    Work.ZeroFreeTables.TentRowCert ((1 : ℝ), (135902 : ℝ)/10^9, (10514 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((1 : ℝ), (65275 : ℝ)/10^9, (11377 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((1 : ℝ), (29593 : ℝ)/10^9, (12297 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((1 : ℝ), (12733 : ℝ)/10^9, (13269 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((1 : ℝ), (5224 : ℝ)/10^9, (14287 : ℝ)/1000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine TentRowCert_of_poly (1 : ℝ) ((135902 : ℝ)/10^9) ((10514 : ℝ)/1000)
      ((1929237794918 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (1 : ℝ) ((65275 : ℝ)/10^9) ((11377 : ℝ)/1000)
      ((2036153522860 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (1 : ℝ) ((29593 : ℝ)/10^9) ((12297 : ℝ)/1000)
      ((2156663820206 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (1 : ℝ) ((12733 : ℝ)/10^9) ((13269 : ℝ)/1000)
      ((2291742625486 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (1 : ℝ) ((5224 : ℝ)/10^9) ((14287 : ℝ)/1000)
      ((2442293361194 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

end Work.ZeroFreeTables
