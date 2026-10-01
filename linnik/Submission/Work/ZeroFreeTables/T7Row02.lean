/-
# ZeroFreeTables — T7Row02

Row `(λ₁, λ₂) = (3/25, 64/25)` of Heath-Brown's Table 7, certified with `k = 481/500`,
`λ = 1203/1250`, `ε = 0` (strict failure of HB (8.11) at these parameters).
Built on `T7Cert`; see the recipe there and the worked instance `T7Row01`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row02 : CertRow (3/25) (64/25) (481/500) (1203/1250) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (208917217/50000000 : ℝ) ≤ (3200/1203 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (3200/1203 : ℝ) * (Real.pi/2) ≤ (83566887/20000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (79649689/20000000 : ℝ) ≤ (3050/1203 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (3050/1203 : ℝ) * (Real.pi/2) ≤ (199124223/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (815721489/12500000 : ℝ) ≤ Real.exp ((3200/1203 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (208917217/50000000) (815721489/12500000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((3200/1203 : ℝ) * (Real.pi/2)) ≤ (3262885989/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (83566887/20000000) (3262885989/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (670626999/12500000 : ℝ) ≤ Real.exp ((3050/1203 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (79649689/20000000) (670626999/12500000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((3050/1203 : ℝ) * (Real.pi/2)) ≤ (5365016047/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (199124223/50000000) (5365016047/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
