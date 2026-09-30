import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators Interval

/-- Reindexing form of the Montgomery–Vaughan mean value hypothesis: if the `L²` mean value
bound holds for every `Fin N`-indexed family of `δ`-separated frequencies, then it holds for an
arbitrary finite set of indices, by enumerating the finset along `Finset.equivFin`. -/
theorem mv_integral_finset (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2) :
    ∀ {ι : Type} (s : Finset ι) (μ : ι → ℝ) (b : ι → ℂ) (δ A B : ℝ),
      0 < δ → A ≤ B →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |μ i - μ j|) →
      (∫ t in A..B, ‖∑ i ∈ s, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2)
        ≤ (B - A + C₀ / δ) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  intro ι s μ b δ A B hδ hAB hsep
  classical
  set N := s.card with hN
  set e : ↥s ≃ Fin N := Finset.equivFin s with he
  set b' : Fin N → ℂ := fun k => b ((e.symm k : ↥s) : ι) with hb'
  set μ' : Fin N → ℝ := fun k => μ ((e.symm k : ↥s) : ι) with hμ'
  have hsep' : ∀ i j : Fin N, i ≠ j → δ ≤ |μ' i - μ' j| := by
    intro i j hij
    have hne : ((e.symm i : ↥s) : ι) ≠ ((e.symm j : ↥s) : ι) := by
      intro h'
      exact hij (e.symm.injective (Subtype.coe_injective h'))
    exact hsep _ (e.symm i).2 _ (e.symm j).2 hne
  have hsum : ∀ t : ℝ, (∑ k : Fin N, b' k * Complex.exp (Complex.I * ((μ' k : ℂ) * (t : ℂ))))
      = ∑ i ∈ s, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ))) := by
    intro t
    rw [← Finset.sum_attach s
          (fun i => b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))),
        ← Finset.univ_eq_attach s]
    rw [← Equiv.sum_comp e.symm (fun x : ↥s =>
          b ((x : ι)) * Complex.exp (Complex.I * ((μ ((x : ι)) : ℂ) * (t : ℂ))))]
  have hS2 : (∑ k : Fin N, ‖b' k‖ ^ 2) = ∑ i ∈ s, ‖b i‖ ^ 2 := by
    rw [← Finset.sum_attach s (fun i => ‖b i‖ ^ 2), ← Finset.univ_eq_attach s]
    rw [← Equiv.sum_comp e.symm (fun x : ↥s => ‖b ((x : ι))‖ ^ 2)]
  have hint : (∫ t in A..B, ‖∑ i ∈ s, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2)
      = ∫ t in A..B,
          ‖∑ k : Fin N, b' k * Complex.exp (Complex.I * ((μ' k : ℂ) * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    show ‖∑ i ∈ s, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2
        = ‖∑ k : Fin N, b' k * Complex.exp (Complex.I * ((μ' k : ℂ) * (t : ℂ)))‖ ^ 2
    rw [← hsum t]
  have hmv := hC₀ δ hδ N μ' b' hsep' A B hAB
  calc (∫ t in A..B, ‖∑ i ∈ s, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2)
      = ∫ t in A..B,
          ‖∑ k : Fin N, b' k * Complex.exp (Complex.I * ((μ' k : ℂ) * (t : ℂ)))‖ ^ 2 := hint
    _ ≤ (B - A + C₀ / δ) * ∑ k : Fin N, ‖b' k‖ ^ 2 := hmv
    _ = (B - A + C₀ / δ) * ∑ i ∈ s, ‖b i‖ ^ 2 := by rw [hS2]

end Work.BMF.mr_direct
