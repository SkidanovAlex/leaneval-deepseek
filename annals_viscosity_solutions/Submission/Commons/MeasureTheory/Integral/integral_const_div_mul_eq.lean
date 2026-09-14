import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.MeasureTheory.Integral

/-- **The integral of `K / (C * t)` over `[T₀, T]`.** -/
theorem integral_const_div_mul_eq {K C T₀ T : ℝ} (h₀ : 0 < T₀) (hT : T₀ ≤ T) :
    ∫ t in T₀..T, K / (C * t) = K / C * (Real.log T - Real.log T₀) := by
  have hTpos : 0 < T := lt_of_lt_of_le h₀ hT
  have hcongr : ∫ t in T₀..T, K / (C * t) = ∫ t in T₀..T, (K / C) * (1 / t) := by
    apply intervalIntegral.integral_congr
    intro t _
    by_cases hC : C = 0
    · subst hC; simp
    · by_cases ht0 : t = 0
      · subst ht0; simp
      · field_simp [hC, ht0]
  rw [hcongr, intervalIntegral.integral_const_mul]
  rw [integral_one_div_of_pos h₀ hTpos, Real.log_div (ne_of_gt hTpos) (ne_of_gt h₀)]

end Commons.MeasureTheory.Integral