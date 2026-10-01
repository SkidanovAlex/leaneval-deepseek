/-
# ZeroFreeTables — T7Row03

Row `(λ₁, λ₂) = (7/50, 239/100)` of Heath-Brown's Table 7, certified with `k = 959/1000`,
`λ = 9497/10000`, `ε = 0` (strict failure of HB (8.11) at these parameters).
Built on `T7Cert`; see the recipe there and the worked instance `T7Row01`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row03 : CertRow (7/50) (239/100) (959/1000) (9497/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (395304119/100000000 : ℝ) ≤ (23900/9497 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (23900/9497 : ℝ) * (Real.pi/2) ≤ (9882603/2500000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (372148229/100000000 : ℝ) ≤ (22500/9497 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (22500/9497 : ℝ) * (Real.pi/2) ≤ (37214823/10000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (651169407/12500000 : ℝ) ≤ Real.exp ((23900/9497 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (395304119/100000000) (651169407/12500000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((23900/9497 : ℝ) * (Real.pi/2)) ≤ (5209355309/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (9882603/2500000) (5209355309/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (2066280263/50000000 : ℝ) ≤ Real.exp ((22500/9497 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (372148229/100000000) (2066280263/50000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((22500/9497 : ℝ) * (Real.pi/2)) ≤ (516570071/12500000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (37214823/10000000) (516570071/12500000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
