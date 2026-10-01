import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Arsinh

namespace Commons.Analysis.Real

/-- Elementary upper bound for `arsinh`: for `x > 0`,
`arsinh x ≤ log (2*x + (2*x)⁻¹)`. -/
theorem arsinh_le_log_two_mul_add_inv {x : ℝ} (hx : 0 < x) :
    Real.arsinh x ≤ Real.log (2*x + (2*x)⁻¹) := by
  rw [Real.arsinh]
  apply Real.log_le_log
  · positivity
  · -- It suffices to compare the arguments of the logarithms.
    have hpos : (0:ℝ) ≤ x + (2*x)⁻¹ := by positivity
    have hsqrt : Real.sqrt (1 + x^2) ≤ x + (2*x)⁻¹ := by
      rw [Real.sqrt_le_left hpos]
      have h2x : (2:ℝ)*x ≠ 0 := by positivity
      have hsq : (x + (2*x)⁻¹)^2 = x^2 + 1 + ((2*x)⁻¹)^2 := by
        field_simp
        ring
      rw [hsq]
      have := sq_nonneg ((2*x)⁻¹)
      linarith
    linarith

end Commons.Analysis.Real