/-
# ZeroFreeTables — T7Row01

Row `(λ₁, λ₂) = (0.10, 2.76)` of Heath-Brown's Table 7, certified with
`k = 0.965`, `λ = 0.9758`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.

This is the template for `T7Row02` … `T7Row16`: the data used (see the comment in
`T7Cert`) are the rational bounds on `π/2`, `π-3`, `(π/2-2)²` from `T7Cert`, the
rational bounds `q1lo ≤ (c/λ)(π/2) ≤ q1hi` (from `Real.pi_gt_d20`, `Real.pi_lt_d20`),
and the two-sided Taylor bounds on `exp` from `exp_lower` / `exp_upper`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row01 : CertRow (10/100) (276/100) (965/1000) (9758/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (444291643/100000000 : ℝ) ≤ (13800/4879 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (13800/4879 : ℝ) * (Real.pi/2) ≤ (111072911/25000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (10704853/2500000 : ℝ) ≤ (1900/697 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (1900/697 : ℝ) * (Real.pi/2) ≤ (428194121/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (8502254273/100000000 : ℝ) ≤ Real.exp ((13800/4879 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (444291643/100000000) (8502254273/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((13800/4879 : ℝ) * (Real.pi/2)) ≤ (8502254359/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (111072911/25000000) (8502254359/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (3619040467/50000000 : ℝ) ≤ Real.exp ((1900/697 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (10704853/2500000) (3619040467/50000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((1900/697 : ℝ) * (Real.pi/2)) ≤ (452380063/6250000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (428194121/100000000) (452380063/6250000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
