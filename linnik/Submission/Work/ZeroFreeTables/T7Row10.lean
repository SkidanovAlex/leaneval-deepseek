/-
# ZeroFreeTables — T7Row10

Row `(b, c) = (40/100, 129/100)` of Heath-Brown's Table 7, certified with
`k = 0.92`, `λ = 0.8331`, `ε = 0`: the certificate is the strict failure of
HB (8.11) at these parameters.

Same three-step recipe as `T7Row01` (see the comment in `T7Cert`):

1. `CertRow_of_PhiS` strips the denominators of `phiNeg` and reduces the row to a
   *linear* inequality in the atoms `π/2`, `π-3`, `(π/2-2)²`,
   `exp((c/λ)(π/2)) = exp((4300/2777)(π/2))` and
   `exp(((c-b)/λ)(π/2)) = exp((8900/8331)(π/2))`;
2. the interval bounds on those atoms are supplied by `pi_div_two_bounds`,
   `pi_sub_three_bounds`, `s_bounds`, `exp_lower`/`exp_upper` (Taylor bounds for
   `Real.exp` composed with a rational enclosure of the exponent);
3. `unfold ... ; norm_num ; linarith`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row10 : CertRow (40/100) (129/100) (92/100) (8331/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (1945819/800000 : ℝ) ≤ (4300/2777 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (4300/2777 : ℝ) * (Real.pi/2) ≤ (15201711/6250000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (167808033/100000000 : ℝ) ≤ (8900/8331 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (8900/8331 : ℝ) * (Real.pi/2) ≤ (83904017/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (71154617/6250000 : ℝ) ≤ Real.exp ((4300/2777 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (1945819/800000) (71154617/6250000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((4300/2777 : ℝ) * (Real.pi/2)) ≤ (284618471/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (15201711/6250000) (284618471/25000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (21421063/4000000 : ℝ) ≤ Real.exp ((8900/8331 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (167808033/100000000) (21421063/4000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((8900/8331 : ℝ) * (Real.pi/2)) ≤ (535526581/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (83904017/50000000) (535526581/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
