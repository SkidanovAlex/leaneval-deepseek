import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Integral

open MeasureTheory Set intervalIntegral

/-- For `0 ≤ A`, `0 ≤ c` and `-1 < r`, the Lebesgue (lower) integral of the nonnegative
function `t ↦ ENNReal.ofReal (c * t ^ r)` over the interval `(0, A]` is
`ENNReal.ofReal (c * A ^ (r + 1) / (r + 1))`. -/
theorem lintegral_Ioc_ofReal_const_mul_rpow
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) {r : ℝ} (hr : -1 < r) :
    ∫⁻ t in Set.Ioc 0 A, ENNReal.ofReal (c * t ^ r)
      = ENNReal.ofReal (c * (A ^ (r + 1) / (r + 1))) := by
  -- Integrability of `t ↦ c * t ^ r` on `(0, A]`, from `-1 < r`.
  have hint : IntegrableOn (fun t : ℝ => c * t ^ r) (Set.Ioc 0 A) volume := by
    have h0 : IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioc 0 A) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact intervalIntegrable_rpow' hr (a := 0) (b := A)
    exact h0.const_mul c
  -- Nonnegativity a.e. on `(0, A]`.
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 A)] fun t => c * t ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg hc (Real.rpow_nonneg ht.1.le r)
  -- Convert the lower integral into `ENNReal.ofReal` of the Bochner integral.
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  -- Evaluate the Bochner integral using the antiderivative of `t ↦ t ^ r`.
  rw [← integral_of_le hA, intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
      Real.zero_rpow (by linarith : (r + 1) ≠ 0), sub_zero]

end Commons.Analysis.Integral