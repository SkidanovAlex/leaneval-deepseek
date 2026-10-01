/-
# ZeroFreeTables — T7Row08

Row `(λ₁, λ₂) = (3/10, 79/50)` of Heath-Brown's Table 7, certified with `k = 187/200`,
`λ = 349/400`, `ε = 0` (strict failure of HB (8.11) at these parameters).
Built on `T7Cert`; see the recipe there and the worked instance `T7Row01`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row08 : CertRow (3/10) (79/50) (187/200) (349/400) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (284453661/100000000 : ℝ) ≤ (632/349 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (632/349 : ℝ) * (Real.pi/2) ≤ (142226831/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (14402717/6250000 : ℝ) ≤ (512/349 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (512/349 : ℝ) * (Real.pi/2) ≤ (230443473/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (429839737/25000000 : ℝ) ≤ Real.exp ((632/349 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (284453661/100000000) (429839737/25000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((632/349 : ℝ) * (Real.pi/2)) ≤ (859679483/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (142226831/50000000) (859679483/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (500925669/50000000 : ℝ) ≤ Real.exp ((512/349 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (14402717/6250000) (500925669/50000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((512/349 : ℝ) * (Real.pi/2)) ≤ (1001851349/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (230443473/100000000) (1001851349/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
