import Mathlib

namespace Work.WilE3.Taylor.CaseII

/-- The function `z ↦ g z * exp (∑ i, v i * (z i - y i))` is strictly differentiable at `u`
whenever `g` is `C^1` at `u`: the exponential factor is smooth everywhere, and a `C^1` function
has a strict derivative at a point (its derivative is automatically continuous there). -/
theorem aux_hasStrictFDerivAt_mul_exp_sum {k : ℕ} {g : (Fin k → ℝ) → ℝ}
    {v y u : Fin k → ℝ} (hg : ContDiffAt ℝ 1 g u) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => g z * Real.exp (∑ i, v i * (z i - y i)))
      (fderiv ℝ (fun z : Fin k → ℝ => g z * Real.exp (∑ i, v i * (z i - y i))) u) u := by
  have hh : ContDiffAt ℝ 1 (fun z : Fin k → ℝ => Real.exp (∑ i, v i * (z i - y i))) u := by
    fun_prop
  exact (hg.mul hh).hasStrictFDerivAt one_ne_zero

end Work.WilE3.Taylor.CaseII
