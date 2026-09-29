import Mathlib

namespace Work.CAsm

/-- `log (82368/629)` is decomposed using `82368/629 = 2^7 * (131/128) * (82368/82399)`, and each
of the three pieces is bounded by telescoping `log x ≥ 1 - x⁻¹` around the explicit value of
`log 2` supplied by Mathlib. -/
theorem log_bound : (3 / 5 : ℝ) + 1032659 / 242760 < Real.log ((82368 : ℝ) / 629) := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : (3 : ℝ) / 131 ≤ Real.log ((131 : ℝ) / 128) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (131 : ℝ) / 128) (by norm_num)
    norm_num at h
    linarith
  have h3 : -(31 : ℝ) / 82368 ≤ Real.log ((82368 : ℝ) / 82399) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (82368 : ℝ) / 82399) (by norm_num)
    norm_num at h
    linarith
  have hkey : Real.log ((82368 : ℝ) / 629)
      = 7 * Real.log 2 + Real.log ((131 : ℝ) / 128) + Real.log ((82368 : ℝ) / 82399) := by
    have hprod : ((82368 : ℝ) / 629) = 2 ^ 7 * ((131 : ℝ) / 128) * ((82368 : ℝ) / 82399) := by
      norm_num
    rw [hprod, Real.log_mul, Real.log_mul, Real.log_pow]
    · norm_num
    all_goals norm_num
  have hnum : (3 / 5 : ℝ) + 1032659 / 242760
      < 7 * 0.6931471803 + (3 : ℝ) / 131 - 31 / 82368 := by norm_num
  rw [hkey]
  linarith

end Work.CAsm
