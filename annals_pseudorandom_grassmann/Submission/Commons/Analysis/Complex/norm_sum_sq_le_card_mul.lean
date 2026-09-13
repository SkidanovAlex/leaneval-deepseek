import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Complex

/-- Cauchy–Schwarz: the squared norm of a finite sum of complex numbers is at most the
cardinality of the index set times the sum of the squared norms. -/
theorem norm_sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
    nlinarith [h1, norm_nonneg (∑ i ∈ s, f i),
      Finset.sum_nonneg (s := s) fun i _ => norm_nonneg (f i)]
  have h3 : (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖)
  linarith

end Commons.Analysis.Complex