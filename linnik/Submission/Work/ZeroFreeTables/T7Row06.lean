/-
# ZeroFreeTables — T7Row06

Row `(λ₁, λ₂) = (1/5, 201/100)` of Heath-Brown's Table 7, certified with `k = 19/20`,
`λ = 9187/10000`, `ε = 0` (strict failure of HB (8.11) at these parameters).
Built on `T7Cert`; see the recipe there and the worked instance `T7Row01`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row06 : CertRow (1/5) (201/100) (19/20) (9187/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (34367047/10000000 : ℝ) ≤ (20100/9187 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (20100/9187 : ℝ) * (Real.pi/2) ≤ (343670471/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (77368601/25000000 : ℝ) ≤ (18100/9187 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (18100/9187 : ℝ) * (Real.pi/2) ≤ (61894881/20000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (777108923/25000000 : ℝ) ≤ Real.exp ((20100/9187 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (34367047/10000000) (777108923/25000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((20100/9187 : ℝ) * (Real.pi/2)) ≤ (777108931/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (343670471/100000000) (777108931/25000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (2208158581/100000000 : ℝ) ≤ Real.exp ((18100/9187 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (77368601/25000000) (2208158581/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((18100/9187 : ℝ) * (Real.pi/2)) ≤ (552039651/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (61894881/20000000) (552039651/25000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
