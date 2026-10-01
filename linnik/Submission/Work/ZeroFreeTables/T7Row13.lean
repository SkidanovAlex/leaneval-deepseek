/-
# ZeroFreeTables — T7Row13

Row `(λ₁, λ₂) = (0.55, 1.00)` of Heath-Brown's Table 7, certified with
`k = 0.8975`, `λ = 0.7848`, `ε = 0`; the certificate is the strict failure of
HB (8.11) at these parameters.  Same three-step recipe as `T7Row01` (see the
comment at the end of `T7Cert`).

Here `c = 1`, so `c/λ = 1250/981` and `(c-b)/λ = 125/218`.
-/
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

theorem T7Row13 : CertRow (55/100) (100/100) (8975/10000) (7848/10000) 0 := by
  apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (200152437/100000000 : ℝ) ≤ (1250/981 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (1250/981 : ℝ) * (Real.pi/2) ≤ (100076219/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hq2lo : (22517149/25000000 : ℝ) ≤ (125/218 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (125/218 : ℝ) * (Real.pi/2) ≤ (90068597/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have he1lo : (370016417/50000000 : ℝ) ≤ Real.exp ((1250/981 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (200152437/100000000) (370016417/50000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have he1hi : Real.exp ((1250/981 : ℝ) * (Real.pi/2)) ≤ (370016421/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (100076219/50000000) (370016421/50000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have he2lo : (246129087/100000000 : ℝ) ≤ Real.exp ((125/218 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (22517149/25000000) (246129087/100000000) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have he2hi : Real.exp ((125/218 : ℝ) * (Real.pi/2)) ≤ (246129091/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (90068597/100000000) (246129091/100000000) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD psi87
  norm_num
  linarith

end Work.ZeroFreeTables
