/-
# ZeroFreeTables — T7Row04

Row `(λ₁, λ₂) = (4/25, 9/4)` of Heath-Brown's Table 7, certified with `k = 239/250`,
`λ = 1879/2000`, `ε = 0` (strict failure of HB (8.11) at these parameters).
Built on `T7Cert`; see the recipe there and the worked instance `T7Row01`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row04 : CertRow (4/25) (9/4) (239/250) (1879/2000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (188094291/50000000 : ℝ) ≤ (4500/1879 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (4500/1879 : ℝ) * (Real.pi/2) ≤ (376188583/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (174718697/50000000 : ℝ) ≤ (4180/1879 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (4180/1879 : ℝ) * (Real.pi/2) ≤ (69887479/20000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (4302949539/100000000 : ℝ) ≤ Real.exp ((4500/1879 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (188094291/50000000) (4302949539/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((4500/1879 : ℝ) * (Real.pi/2)) ≤ (4302949583/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (376188583/100000000) (4302949583/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (658593311/20000000 : ℝ) ≤ Real.exp ((4180/1879 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (174718697/50000000) (658593311/20000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((4180/1879 : ℝ) * (Real.pi/2)) ≤ (3292966589/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (69887479/20000000) (3292966589/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
