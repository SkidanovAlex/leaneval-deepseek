import Mathlib.Analysis.CStarAlgebra.Classes

set_option linter.unusedVariables false

namespace Commons.Analysis.DiscreteCZ

/-- Swapping the order of a finite double sum against a continuous linear functional:
the pairing of the finite convolution `x ↦ ∑ y ∈ t, K (x - y) • f y` with the dual
family `Φ` equals the pairing of `f` with the dual convolution `y ↦ ∑ x ∈ s, K (x - y) • Φ x`.
The support hypotheses `hf`, `hΦ` are not needed for the identity but are part of the
interface requested by the caller. -/
theorem sum_dual_pairing {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : ℤ → ℂ) (Φ : ℤ → (H →L[ℂ] ℂ)) (f : ℤ → H) (s t : Finset ℤ)
    (hf : ∀ x, x ∉ t → f x = 0) (hΦ : ∀ x, x ∉ s → Φ x = 0) :
    ∑ x ∈ s, Φ x (∑ y ∈ t, K (x - y) • f y)
      = ∑ y ∈ t, (∑ x ∈ s, K (x - y) • Φ x) (f y) := by
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  exact Finset.sum_comm

end Commons.Analysis.DiscreteCZ