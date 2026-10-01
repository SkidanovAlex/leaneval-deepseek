import Mathlib
import Submission.Work.ZeroFreeTables.TentRowAux

namespace Work.ZeroFreeTables

/-- Row certificates 17-21 of `Work.ZeroFreeTables.tentRows`.  Recipe (constants `B = n/10^12` and
the one-line proof template): see the table in `Submission/Work/ZeroFreeTables/TentRowAux.lean`,
mathlib module `Submission.Work.ZeroFreeTables.TentRowAux`; here `n = 1592984618182, 1655329363158,
1725201318413, 1802748599598, 1835147757385` in that order. -/
theorem TentRowsB5 :
    Work.ZeroFreeTables.TentRowCert ((21/20 : ℝ), (2450410 : ℝ)/10^9, (7095 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((21/20 : ℝ), (1499186 : ℝ)/10^9, (7680 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((21/20 : ℝ), (876931 : ℝ)/10^9, (8310 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((21/20 : ℝ), (492221 : ℝ)/10^9, (8980 : ℝ)/1000) ∧
    Work.ZeroFreeTables.TentRowCert ((1 : ℝ), (266337 : ℝ)/10^9, (9714 : ℝ)/1000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- row 17 of `tentRows`: X = 21/20, b = 2450410/10⁹, c = 7095/1000, B = 1592984618182/10¹²
    refine TentRowCert_of_poly (21/20 : ℝ) ((2450410 : ℝ)/10^9) ((7095 : ℝ)/1000)
      ((1592984618182 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · -- row 18 of `tentRows`: X = 21/20, b = 1499186/10⁹, c = 7680/1000, B = 1655329363158/10¹²
    refine TentRowCert_of_poly (21/20 : ℝ) ((1499186 : ℝ)/10^9) ((7680 : ℝ)/1000)
      ((1655329363158 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · -- row 19 of `tentRows`: X = 21/20, b = 876931/10⁹, c = 8310/1000, B = 1725201318413/10¹²
    refine TentRowCert_of_poly (21/20 : ℝ) ((876931 : ℝ)/10^9) ((8310 : ℝ)/1000)
      ((1725201318413 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · -- row 20 of `tentRows`: X = 21/20, b = 492221/10⁹, c = 8980/1000, B = 1802748599598/10¹²
    refine TentRowCert_of_poly (21/20 : ℝ) ((492221 : ℝ)/10^9) ((8980 : ℝ)/1000)
      ((1802748599598 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
  · -- row 21 of `tentRows`: X = 1, b = 266337/10⁹, c = 9714/1000, B = 1835147757385/10¹²
    refine TentRowCert_of_poly (1 : ℝ) ((266337 : ℝ)/10^9) ((9714 : ℝ)/1000)
      ((1835147757385 : ℝ)/10^12)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

end Work.ZeroFreeTables
