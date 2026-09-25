import Mathlib

namespace Work.CMRealSubfield.RealSubfield

open NumberField

/-- For a CM field `K`, the degree of `K` over `ℚ` is twice the degree of its maximal real
subfield `K⁺` (Mathlib's `NumberField.IsCMField.is_quadratic` provides the quadratic extension
`K⁺ / K`).  Consequently a lower bound `2 * N ≤ [K : ℚ]` yields `N ≤ [K⁺ : ℚ]`. -/
theorem le_finrank_maximalRealSubfield_of_two_mul_le (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] {N : ℕ} (hN : 2 * N ≤ Module.finrank ℚ K) :
    N ≤ Module.finrank ℚ (NumberField.maximalRealSubfield K) := by
  have h2 : Module.finrank ℚ K = 2 * Module.finrank ℚ (NumberField.maximalRealSubfield K) := by
    rw [← Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield K) K]
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield K) K,
      mul_comm]
  omega

end Work.CMRealSubfield.RealSubfield
