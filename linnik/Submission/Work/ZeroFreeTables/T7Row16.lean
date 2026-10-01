/-
# ZeroFreeTables — T7Row16

Row `(λ₁, λ₂) = (0.70, 0.79)` of Heath-Brown's Table 7, certified with
`k = 0.875`, `λ = 0.7371`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.

Data lifted from the table in `T7Cert`: `m1 = c/λ = 7900/7371`,
`m2 = (c-b)/λ = 100/819`, with the rational interval bounds on
`m·(π/2)` (from `Real.pi_gt_d20`, `Real.pi_lt_d20`) and the corresponding
two-sided Taylor bounds on `exp`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row16 : CertRow (70/100) (79/100) (875/1000) (7371/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (84176441/50000000 : ℝ) ≤ (7900/7371 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (7900/7371 : ℝ) * (Real.pi/2) ≤ (168352883/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (9589721/50000000 : ℝ) ≤ (100/819 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (100/819 : ℝ) * (Real.pi/2) ≤ (19179443/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (538452349/100000000 : ℝ) ≤ Real.exp ((7900/7371 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (84176441/50000000) (538452349/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((7900/7371 : ℝ) * (Real.pi/2)) ≤ (134613089/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (168352883/100000000) (134613089/25000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (946423/781250 : ℝ) ≤ Real.exp ((100/819 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (9589721/50000000) (946423/781250) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((100/819 : ℝ) * (Real.pi/2)) ≤ (60571073/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (19179443/100000000) (60571073/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
