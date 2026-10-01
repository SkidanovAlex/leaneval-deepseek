import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Integral

/-- `τ ↦ (a² + (τ - b)²)⁻¹` is integrable on `ℝ` for every nonzero `a`; it is a
translate-and-scale of `x ↦ (1 + x²)⁻¹`. -/
theorem integrable_inv_sq_add (a b : ℝ) (ha : a ≠ 0) :
    MeasureTheory.Integrable (fun t : ℝ => (a ^ 2 + (t - b) ^ 2)⁻¹) := by
  -- Rescale `(1 + x²)⁻¹` by `a` and translate by `b`.
  have hbase : MeasureTheory.Integrable (fun t : ℝ => (1 + ((t - b) / a) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div ha).comp_sub_right b
  -- Rewrite the integrand as the constant multiple `(a²)⁻¹ * (1 + ((t-b)/a)²)⁻¹`.
  refine (hbase.const_mul (a ^ 2)⁻¹).congr (Filter.Eventually.of_forall fun t => ?_)
  change (a ^ 2)⁻¹ * (1 + ((t - b) / a) ^ 2)⁻¹ = (a ^ 2 + (t - b) ^ 2)⁻¹
  rw [div_pow]
  field_simp

end Commons.Analysis.Integral
