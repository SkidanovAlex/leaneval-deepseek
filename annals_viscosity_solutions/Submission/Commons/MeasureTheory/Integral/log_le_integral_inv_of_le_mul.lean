import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

namespace Commons.MeasureTheory.Integral

/-- **Divergence of the integral of `1/ρ`.**  If `0 < ρ t ≤ C * t` on `[T₀, T]` with `0 < T₀ ≤ T`,
`0 < C`, and `1/ρ` is interval integrable on `[T₀, T]`, then
`(log T - log T₀)/C ≤ ∫_{T₀}^{T} 1/ρ`. -/
theorem log_le_integral_inv_of_le_mul {ρ : ℝ → ℝ} {T₀ T C : ℝ} (h₀ : 0 < T₀) (hT : T₀ ≤ T)
    (hC : 0 < C) (hρ : ∀ t ∈ Set.Icc T₀ T, 0 < ρ t)
    (hρC : ∀ t ∈ Set.Icc T₀ T, ρ t ≤ C * t)
    (hint : IntervalIntegrable (fun t => (ρ t)⁻¹) MeasureTheory.volume T₀ T) :
    (Real.log T - Real.log T₀) / C ≤ ∫ t in T₀..T, (ρ t)⁻¹ := by
  have hTpos : 0 < T := lt_of_lt_of_le h₀ hT
  -- `1/(C t)` is interval integrable, since `C t ≠ 0` on `[T₀, T]`
  have hintCt : IntervalIntegrable (fun t => (C * t)⁻¹) MeasureTheory.volume T₀ T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le h₀ hx.1
      exact ne_of_gt (mul_pos hC hx0)
  -- pointwise comparison `1/(C t) ≤ 1/ρ t`
  have hpt : ∀ x ∈ Set.Icc T₀ T, (C * x)⁻¹ ≤ (ρ x)⁻¹ := by
    intro x hx
    have h := one_div_le_one_div_of_le (hρ x hx) (hρC x hx)
    simpa only [one_div] using h
  have hmono : ∫ t in T₀..T, (C * t)⁻¹ ≤ ∫ t in T₀..T, (ρ t)⁻¹ :=
    intervalIntegral.integral_mono_on hT hintCt hint hpt
  -- computation of `∫_{T₀}^{T} 1/(C t) dt`
  have hIntCt : ∫ t in T₀..T, (C * t)⁻¹ = C⁻¹ * (Real.log T - Real.log T₀) := by
    have h1 : ∫ t in T₀..T, (C * t)⁻¹ = ∫ t in T₀..T, C⁻¹ * (t : ℝ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t _
      show (C * t)⁻¹ = C⁻¹ * (t : ℝ)⁻¹
      rw [mul_inv_rev, mul_comm]
    rw [h1, intervalIntegral.integral_const_mul, integral_inv_of_pos h₀ hTpos,
      Real.log_div (ne_of_gt hTpos) (ne_of_gt h₀)]
  calc (Real.log T - Real.log T₀) / C
      = C⁻¹ * (Real.log T - Real.log T₀) := by rw [div_eq_mul_inv, mul_comm]
    _ = ∫ t in T₀..T, (C * t)⁻¹ := hIntCt.symm
    _ ≤ ∫ t in T₀..T, (ρ t)⁻¹ := hmono

end Commons.MeasureTheory.Integral
