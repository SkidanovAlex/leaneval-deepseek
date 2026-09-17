import Mathlib.Probability.Distributions.Gaussian.Real

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- The fourth derivative at `0` of `t ↦ exp (t ^ 2 / 2)` equals `3`; equivalently, the fourth
cumulant-free moment of the standard Gaussian in one dimension. -/
private lemma iteratedDeriv_four_exp_half_sq :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 3 := by
  have d0 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_exp (by fun_prop)]
    simp [deriv_div_const, mul_comm]
  have d1 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
      = fun t => (t ^ 2 + 1) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [deriv_exp (by fun_prop)]
    rw [deriv_div_const]
    rw [(hasDerivAt_pow 2 t).deriv]
    simp
    ring
  have d2 : deriv (fun t : ℝ => (t ^ 2 + 1) * Real.exp (t ^ 2 / 2))
      = fun t => (t ^ 3 + 3 * t) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [deriv_exp (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_div_const]
    rw [(hasDerivAt_pow 2 t).deriv]
    rw [deriv_const]
    ring
  have d3 : deriv (fun t : ℝ => (t ^ 3 + 3 * t) * Real.exp (t ^ 2 / 2))
      = fun t => (t ^ 4 + 6 * t ^ 2 + 3) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [deriv_exp (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_div_const]
    rw [(hasDerivAt_pow 3 t).deriv]
    rw [deriv_const_mul_id]
    rw [(hasDerivAt_pow 2 t).deriv]
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [d0, d1, d2, d3]
  norm_num

/-- The fourth moment of the standard real Gaussian `gaussianReal 0 1` is `3`. -/
theorem fourth_moment_gaussianReal :
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) = 3 := by
  have hmem : 0 ∈ interior (integrableExpSet id (ProbabilityTheory.gaussianReal 0 1)) := by simp
  have h := iteratedDeriv_mgf_zero hmem 4
  rw [mgf_id_gaussianReal] at h
  have hfun : (fun t : ℝ => Real.exp (0 * t + (1 : ℝ≥0) * t ^ 2 / 2))
      = (fun t : ℝ => Real.exp (t ^ 2 / 2)) := by funext t; simp
  rw [hfun] at h
  rw [iteratedDeriv_four_exp_half_sq] at h
  exact h.symm

end

end Commons.Probability.Gaussian