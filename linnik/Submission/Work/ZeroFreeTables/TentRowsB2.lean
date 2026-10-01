import Mathlib
import Submission.Work.ZeroFreeTables.TentRowAux

namespace Work.ZeroFreeTables

/-- Row certificates 2-6 of `Work.ZeroFreeTables.tentRows`.  Recipe (constants `B = n/10^12` and
the one-line proof template): see the table in `Submission/Work/ZeroFreeTables/TentRowAux.lean`,
mathlib module `Submission.Work.ZeroFreeTables.TentRowAux`; here `n = 1245952129145, 1255896926764,
1267155975604, 1266950079487, 1281143610821` in that order. -/
theorem TentRowsB2 :
    Work.ZeroFreeTables.TentRowCert ((6/5 : ℝ), (74094301 : ℝ)/10^9, (2932 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((6/5 : ℝ), (68101912 : ℝ)/10^9, (3038 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((6/5 : ℝ), (61795999 : ℝ)/10^9, (3157 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((23/20 : ℝ), (55409734 : ℝ)/10^9, (3292 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((23/20 : ℝ), (48960081 : ℝ)/10^9, (3447 : ℝ)/1000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine TentRowCert_of_poly (6/5 : ℝ) ((74094301 : ℝ)/10^9) ((2932 : ℝ)/1000)
      ((1245952129145 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (6/5 : ℝ) ((68101912 : ℝ)/10^9) ((3038 : ℝ)/1000)
      ((1255896926764 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (6/5 : ℝ) ((61795999 : ℝ)/10^9) ((3157 : ℝ)/1000)
      ((1267155975604 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (23/20 : ℝ) ((55409734 : ℝ)/10^9) ((3292 : ℝ)/1000)
      ((1266950079487 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (23/20 : ℝ) ((48960081 : ℝ)/10^9) ((3447 : ℝ)/1000)
      ((1281143610821 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

end Work.ZeroFreeTables
