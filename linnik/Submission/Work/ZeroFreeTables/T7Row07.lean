/-
# ZeroFreeTables — T7Row07

Row `(λ₁, λ₂) = (1/4, 177/100)` of Heath-Brown's Table 7, certified with `k = 377/400`,
`λ = 4471/5000`, `ε = 0` (strict failure of HB (8.11) at these parameters).
Built on `T7Cert`; see the recipe there and the worked instance `T7Row01`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row07 : CertRow (1/4) (177/100) (377/400) (4471/5000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (310927029/100000000 : ℝ) ≤ (8850/4471 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (8850/4471 : ℝ) * (Real.pi/2) ≤ (31092703/10000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (133505391/50000000 : ℝ) ≤ (7600/4471 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (7600/4471 : ℝ) * (Real.pi/2) ≤ (267010783/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (44809379/2000000 : ℝ) ≤ Real.exp ((8850/4471 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (310927029/100000000) (44809379/2000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((8850/4471 : ℝ) * (Real.pi/2)) ≤ (1120234487/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (31092703/10000000) (1120234487/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (1444152619/100000000 : ℝ) ≤ Real.exp ((7600/4471 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (133505391/50000000) (1444152619/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((7600/4471 : ℝ) * (Real.pi/2)) ≤ (722076317/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (267010783/100000000) (722076317/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
