import Mathlib
import Submission.Work.ZeroFreeTables.TentRowAux

namespace Work.ZeroFreeTables

/-- Row certificates 12-16 of `Work.ZeroFreeTables.tentRows`.  Recipe (constants `B = n/10^12` and
the one-line proof template): see the table in `Submission/Work/ZeroFreeTables/TentRowAux.lean`,
mathlib module `Submission.Work.ZeroFreeTables.TentRowAux`; here `n = 1400275145765, 1434969722951,
1474066635494, 1489844683110, 1537925414833` in that order. -/
theorem TentRowsB4 :
    Work.ZeroFreeTables.TentRowCert ((11/10 : ℝ), (15075767 : ℝ)/10^9, (4897 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((11/10 : ℝ), (11243108 : ℝ)/10^9, (5253 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((11/10 : ℝ), (8112629 : ℝ)/10^9, (5644 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((21/20 : ℝ), (5668958 : ℝ)/10^9, (6075 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((21/20 : ℝ), (3818746 : ℝ)/10^9, (6559 : ℝ)/1000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine TentRowCert_of_poly (11/10 : ℝ) ((15075767 : ℝ)/10^9) ((4897 : ℝ)/1000)
      ((1400275145765 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (11/10 : ℝ) ((11243108 : ℝ)/10^9) ((5253 : ℝ)/1000)
      ((1434969722951 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (11/10 : ℝ) ((8112629 : ℝ)/10^9) ((5644 : ℝ)/1000)
      ((1474066635494 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (21/20 : ℝ) ((5668958 : ℝ)/10^9) ((6075 : ℝ)/1000)
      ((1489844683110 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · refine TentRowCert_of_poly (21/20 : ℝ) ((3818746 : ℝ)/10^9) ((6559 : ℝ)/1000)
      ((1537925414833 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

end Work.ZeroFreeTables
