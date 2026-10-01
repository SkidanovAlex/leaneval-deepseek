import Mathlib

namespace Work.LinnikAreas

/-- Cauchy–Schwarz / Jensen in the form needed for Linnik's theorem:
the squared norm of a finite sum of complex numbers is at most the cardinality
of the index set times the sum of the squared norms. -/
theorem norm_sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le s z
  have h2 : ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (∑ i ∈ s, ‖z i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact h2.trans h3

end Work.LinnikAreas
