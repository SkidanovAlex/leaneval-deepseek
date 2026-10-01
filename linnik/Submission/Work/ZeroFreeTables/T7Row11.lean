/-
# ZeroFreeTables — T7Row11

Row `(b, c, k, λ) = (0.45, 1.18, 0.9125, 0.8164)` of Heath-Brown's Table 7,
certified with `ε = 0`; the certificate is the strict failure of HB (8.11) at
these parameters.

Same three-step recipe as `T7Row01` (see the comment in `T7Cert`): reduce to the
linear inequality in the atoms via `CertRow_of_PhiS`, bound `π/2`, `π-3`,
`(π/2-2)²` by the rationals from `T7Cert`, bound the two exponentials by the
two-sided Taylor bounds `exp_lower` / `exp_upper`, then `norm_num; linarith`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row11 : CertRow (45/100) (118/100) (9125/10000) (8164/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (9081527/4000000 : ℝ) ≤ (2950/2041 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (2950/2041 : ℝ) * (Real.pi/2) ≤ (7094943/3125000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (7022791/5000000 : ℝ) ≤ (1825/2041 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (1825/2041 : ℝ) * (Real.pi/2) ≤ (140455821/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (968309663/100000000 : ℝ) ≤ Real.exp ((2950/2041 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (9081527/4000000) (968309663/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((2950/2041 : ℝ) * (Real.pi/2)) ≤ (968309673/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (7094943/3125000) (968309673/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (407372657/100000000 : ℝ) ≤ Real.exp ((1825/2041 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (7022791/5000000) (407372657/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((1825/2041 : ℝ) * (Real.pi/2)) ≤ (203686331/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (140455821/100000000) (203686331/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
