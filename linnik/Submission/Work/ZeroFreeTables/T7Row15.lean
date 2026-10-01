/-
# ZeroFreeTables — T7Row15

Row `(λ₁, λ₂) = (0.65, 0.85)` of Heath-Brown's Table 7, certified with
`k = 0.8825`, `λ = 0.7516`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.  Same three-step recipe as `T7Row01` (see the
comment at the end of `T7Cert`): reduce to the linear inequality of
`CertRow_of_PhiS`, bound the atoms `π/2`, `π-3`, `(π/2-2)²` and the two
exponentials by rationals, and close with `linarith`.

The reduced fractions are `c/λ = 2125/1879` and `(c-b)/λ = 500/1879`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row15 : CertRow (65/100) (85/100) (8825/10000) (7516/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (2775697/1562500 : ℝ) ≤ (2125/1879 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (2125/1879 : ℝ) * (Real.pi/2) ≤ (177644609/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (41798731/100000000 : ℝ) ≤ (500/1879 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (500/1879 : ℝ) * (Real.pi/2) ≤ (10449683/25000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (295440979/50000000 : ℝ) ≤ Real.exp ((2125/1879 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (2775697/1562500) (295440979/50000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((2125/1879 : ℝ) * (Real.pi/2)) ≤ (118176393/20000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (177644609/100000000) (118176393/20000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (151890139/100000000 : ℝ) ≤ Real.exp ((500/1879 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (41798731/100000000) (151890139/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((500/1879 : ℝ) * (Real.pi/2)) ≤ (75945071/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (10449683/25000000) (75945071/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
