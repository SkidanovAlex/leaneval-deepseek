import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs

namespace Work.ZeroDensity.LogFree

open scoped BigOperators

/-- The mean value theorem `MvtMul C` (stated for `Fin m`-indexed families) for an arbitrary
finite index type: the `δ`-separated frequencies may be indexed by any `Fintype`. -/
theorem HB7MvtAny {C : ℝ} (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∀ (δ : ℝ), 0 < δ → ∀ {ι : Type*} [Fintype ι] (γ : ι → ℝ) (ζ : ι → ℂ) (Y₁ Y₂ : ℝ),
      0 < Y₁ → Y₁ ≤ Y₂ → (∀ i j, i ≠ j → δ ≤ |γ i - γ j|) →
      (∫ y in Y₁..Y₂, ‖∑ i, ζ i * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
        ≤ (Real.log (Y₂ / Y₁) + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
  intro δ hδ ι _ γ ζ Y₁ Y₂ hY₁ hYle hsep
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let γ' : Fin (Fintype.card ι) → ℝ := fun k => γ (e.symm k)
  let ζ' : Fin (Fintype.card ι) → ℂ := fun k => ζ (e.symm k)
  have hsep' : ∀ k l, k ≠ l → δ ≤ |γ' k - γ' l| := by
    intro k l hkl
    have hne : e.symm k ≠ e.symm l := fun h => hkl (e.symm.injective h)
    simpa only [γ'] using hsep (e.symm k) (e.symm l) hne
  have hmain := hMVT δ hδ (Fintype.card ι) γ' ζ' Y₁ Y₂ hY₁ hYle hsep'
  have hsum : ∀ y : ℝ, (∑ i : ι, ζ i * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
      = ∑ k : Fin (Fintype.card ι), ζ' k * (y : ℂ) ^ ((-(γ' k : ℂ)) * Complex.I) := by
    intro y
    rw [← Equiv.sum_comp e.symm
      (fun i : ι => ζ i * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))]
  have hint : (∫ y in Y₁..Y₂,
        ‖∑ i : ι, ζ i * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
      = ∫ y in Y₁..Y₂,
        ‖∑ k : Fin (Fintype.card ι),
            ζ' k * (y : ℂ) ^ ((-(γ' k : ℂ)) * Complex.I)‖ ^ 2 / y := by
    apply intervalIntegral.integral_congr
    intro y _
    simp only [hsum y]
  have hnorm : (∑ i : ι, ‖ζ i‖ ^ 2) = ∑ k : Fin (Fintype.card ι), ‖ζ' k‖ ^ 2 := by
    rw [← Equiv.sum_comp e.symm (fun i : ι => ‖ζ i‖ ^ 2)]
  rw [hint, hnorm]
  exact hmain

end Work.ZeroDensity.LogFree
