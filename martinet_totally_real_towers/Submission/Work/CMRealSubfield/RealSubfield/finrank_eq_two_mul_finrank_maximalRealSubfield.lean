import Mathlib

namespace Work.CMRealSubfield.RealSubfield

open NumberField

/-- For a CM field `K`, the degree over `ℚ` is twice the degree of its maximal real subfield
`K⁺`: `K⁺` is a quadratic extension of `K` (Mathlib's `IsCMField.is_quadratic`), so the tower
formula `[K : ℚ] = [K⁺ : ℚ] · [K : K⁺]` gives the claim. -/
theorem finrank_eq_two_mul_finrank_maximalRealSubfield (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    Module.finrank ℚ K = 2 * Module.finrank ℚ (NumberField.maximalRealSubfield K) := by
  rw [← Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield K) K,
    Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield K) K, mul_comm]

end Work.CMRealSubfield.RealSubfield
