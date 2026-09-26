import Mathlib

namespace Work.Analysis.SqAddSq

/-- The function `τ ↦ (1/√A) * arctan (τ √A / s)` is an antiderivative of
`τ ↦ s / (A τ² + s²)`, for `A > 0`, `s > 0`. -/
private lemma hasDerivAt_model {A s : ℝ} (hA : 0 < A) (hs : 0 < s) (τ : ℝ) :
    HasDerivAt (fun τ => (1 / Real.sqrt A) * Real.arctan (τ * Real.sqrt A / s))
      (s / (A * τ ^ 2 + s ^ 2)) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => τ * Real.sqrt A / s) (Real.sqrt A / s) τ := by
    simpa using ((hasDerivAt_id τ).mul_const (Real.sqrt A)).div_const s
  have h2 := (Real.hasDerivAt_arctan (τ * Real.sqrt A / s)).comp τ h1
  have h3 : HasDerivAt (fun τ => (1 / Real.sqrt A) * Real.arctan (τ * Real.sqrt A / s))
      ((1 / Real.sqrt A) * (1 / (1 + (τ * Real.sqrt A / s) ^ 2) * (Real.sqrt A / s))) τ := by
    simpa only [Function.comp_apply] using h2.const_mul (1 / Real.sqrt A)
  refine h3.congr_deriv ?_
  have hA' : Real.sqrt A ^ 2 = A := Real.sq_sqrt (le_of_lt hA)
  field_simp
  rw [hA']; ring

set_option linter.unusedVariables false in
theorem integral_s_div_sq_add_sq_le {A s ε : ℝ} (hA : 0 < A) (hs : 0 < s) (hε : 0 ≤ ε) :
    ∫ τ in (0 : ℝ)..ε, s / (A * τ ^ 2 + s ^ 2) ≤ (Real.pi / 2) / Real.sqrt A := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) ε,
      HasDerivAt (fun τ => (1 / Real.sqrt A) * Real.arctan (τ * Real.sqrt A / s))
        (s / (A * x ^ 2 + s ^ 2)) x :=
    fun x _ => hasDerivAt_model hA hs x
  have hint : IntervalIntegrable (fun τ : ℝ => s / (A * τ ^ 2 + s ^ 2)) MeasureTheory.volume
      (0 : ℝ) ε := by
    apply Continuous.intervalIntegrable
    apply Continuous.div
    · exact continuous_const
    · exact (continuous_const.mul (continuous_pow 2)).add continuous_const
    · intro τ
      exact ne_of_gt (by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_mul, zero_div, Real.arctan_zero, mul_zero, sub_zero]
  calc (1 / Real.sqrt A) * Real.arctan (ε * Real.sqrt A / s)
      ≤ (1 / Real.sqrt A) * (Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt (Real.arctan_lt_pi_div_two _))
        exact le_of_lt (one_div_pos.mpr (Real.sqrt_pos_of_pos hA))
    _ = (Real.pi / 2) / Real.sqrt A := by rw [one_div_mul_eq_div]

end Work.Analysis.SqAddSq
