/-
# ZeroFreeTables — T7Row14

Row `(λ₁, λ₂) = (0.60, 0.92)` of Heath-Brown's Table 7, certified with
`k = 0.89`, `λ = 0.7677`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.  Same three-step recipe as `T7Row01` (see the
comment at the end of `T7Cert`).
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row14 : CertRow (60/100) (92/100) (89/100) (7677/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (188241841/100000000 : ℝ) ≤ (9200/7677 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (9200/7677 : ℝ) * (Real.pi/2) ≤ (94120921/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (65475423/100000000 : ℝ) ≤ (3200/7677 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (3200/7677 : ℝ) * (Real.pi/2) ≤ (2046107/3125000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (65693731/10000000 : ℝ) ≤ Real.exp ((9200/7677 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (188241841/100000000) (65693731/10000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((9200/7677 : ℝ) * (Real.pi/2)) ≤ (656937317/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (94120921/50000000) (656937317/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (192466943/100000000 : ℝ) ≤ Real.exp ((3200/7677 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (65475423/100000000) (192466943/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((3200/7677 : ℝ) * (Real.pi/2)) ≤ (96233473/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (2046107/3125000) (96233473/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
