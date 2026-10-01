/-
# ZeroFreeTables — T7Row12

Row `(λ₁, λ₂) = (0.50, 1.08)` of Heath-Brown's Table 7, certified with
`k = 0.905`, `λ = 0.7988`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.  Same three-step recipe as `T7Row01` (see the
comment at the end of `T7Cert`).
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row12 : CertRow (50/100) (108/100) (905/1000) (7988/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (53094017/25000000 : ℝ) ≤ (2700/1997 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (2700/1997 : ℝ) * (Real.pi/2) ≤ (212376069/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (57026907/50000000 : ℝ) ≤ (1450/1997 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (1450/1997 : ℝ) * (Real.pi/2) ≤ (22810763/20000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (836252721/100000000 : ℝ) ≤ Real.exp ((2700/1997 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (53094017/25000000) (836252721/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((2700/1997 : ℝ) * (Real.pi/2)) ≤ (83625273/10000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (212376069/100000000) (83625273/10000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (62569029/20000000 : ℝ) ≤ Real.exp ((1450/1997 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (57026907/50000000) (62569029/20000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((1450/1997 : ℝ) * (Real.pi/2)) ≤ (312845149/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (22810763/20000000) (312845149/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
