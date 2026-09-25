import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Integral

open Finset

/-- Given a complex-valued family `u` on a finite type, there is a "unit witness"
`g` (all entries of norm at most `1`) whose pairing with `u` has norm at least
the sum of the norms `∑ᵢ ‖uᵢ‖`.  This is the ℓ∞-duality fact that the norm of
the functional `g ↦ ∑ᵢ uᵢ gᵢ` on the sup-norm unit ball is exactly `∑ᵢ ‖uᵢ‖`:
the maximizer is `gᵢ = conj(uᵢ)/‖uᵢ‖` (and `0` where `uᵢ = 0`), which makes
`uᵢ gᵢ = ‖uᵢ‖` a nonnegative real. -/
theorem exists_unit_witness_l1 {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    ∃ g : ι → ℂ, (∀ i, ‖g i‖ ≤ 1) ∧ (∑ i, ‖u i‖) ≤ ‖∑ i, u i * g i‖ := by
  have key : ∀ i, ∃ g : ℂ, ‖g‖ ≤ 1 ∧ u i * g = (‖u i‖ : ℂ) := by
    intro i
    by_cases h : u i = 0
    · exact ⟨0, by simp [h]⟩
    · refine ⟨starRingEnd ℂ (u i) / (‖u i‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]
      · rw [mul_div_assoc', Complex.mul_conj', div_eq_iff (by simp [norm_ne_zero_iff.mpr h])]
        ring
  choose g hg1 hg2 using key
  refine ⟨g, hg1, ?_⟩
  have hsum : ∑ i, u i * g i = ((∑ i, ‖u i‖ : ℝ) : ℂ) := by
    rw [show (∑ i, u i * g i) = ∑ i, (‖u i‖ : ℂ) from
      Finset.sum_congr rfl (fun i _ => hg2 i)]
    push_cast
    rfl
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]

end Commons.Analysis.Integral