/-
# ZeroFreeTables — T7Row17

The diagonal row `(λ₁, λ₂) = (0.745, 0.745)` of Heath-Brown's Table 7
(certified with `k = 0.8682`, `λ = 0.726`, `ε = 0`).  Here `b = c`, so the second
`tfF` is `tfF λ 0` and the row is handled by `CertRow_eq_of_PhiS`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row17 : CertRow (745/1000) (745/1000) (8682/10000) (726/1000) 0 := by
  apply CertRow_eq_of_PhiS (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (40297633/25000000 : ℝ) ≤ (745/726 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (745/726 : ℝ) * (Real.pi/2) ≤ (161190533/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (501235227/100000000 : ℝ) ≤ Real.exp ((745/726 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (40297633/25000000) (501235227/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((745/726 : ℝ) * (Real.pi/2)) ≤ (501235233/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (161190533/100000000) (501235233/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
