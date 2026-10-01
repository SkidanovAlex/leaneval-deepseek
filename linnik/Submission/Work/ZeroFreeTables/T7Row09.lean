/-
# ZeroFreeTables — T7Row09

Row `(λ₁, λ₂) = (0.35, 1.42)` of Heath-Brown's Table 7, certified with
`k = 0.9275`, `λ = 0.8514`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row09 : CertRow (35/100) (142/100) (9275/10000) (8514/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hq1lo : (261983883/100000000 : ℝ) ≤ (7100/4257 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (7100/4257 : ℝ) * (Real.pi/2) ≤ (65495971/25000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (197410391/100000000 : ℝ) ≤ (5350/4257 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (5350/4257 : ℝ) * (Real.pi/2) ≤ (24676299/12500000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (1373350997/100000000 : ℝ) ≤ Real.exp ((7100/4257 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (261983883/100000000) (1373350997/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((7100/4257 : ℝ) * (Real.pi/2)) ≤ (343337753/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (65495971/25000000) (343337753/25000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (180004119/25000000 : ℝ) ≤ Real.exp ((5350/4257 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (197410391/100000000) (180004119/25000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((5350/4257 : ℝ) * (Real.pi/2)) ≤ (180004121/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (24676299/12500000) (180004121/25000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
