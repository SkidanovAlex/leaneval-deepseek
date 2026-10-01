import Mathlib

namespace Work.LinnikAreas.A5

/-- Helper: the derivative of `t ↦ Real.exp (-t)` at `0` is `-1`. -/
private lemma hasDerivAt_exp_neg_zero :
    HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
  simpa using (hasDerivAt_neg (0 : ℝ)).exp

theorem Baux_lim_ratio :
    Filter.Tendsto (fun t : ℝ => (1 - Real.exp (-t)) / t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  -- `(1 - exp(-t))/t` is minus the slope quotient `(exp(-t) - exp 0)/(t - 0)`.
  have h := hasDerivAt_exp_neg_zero.tendsto_slope_zero_right
  have h2 : (fun t : ℝ => (1 - Real.exp (-t)) / t)
      = fun t : ℝ => -(t⁻¹ • (Real.exp (-(0 + t)) - Real.exp (-0))) := by
    funext t
    simp only [div_eq_mul_inv, zero_add, neg_zero, Real.exp_zero, smul_eq_mul]
    ring
  rw [h2]
  simpa using h.neg

end Work.LinnikAreas.A5
