import Mathlib
import Submission.Work.Analysis.IonescuWainger.Symbol
import Submission.Port.Aesm

/-!
# The operator norm of an Ionescu–Wainger projection on non-aliasing frequencies

This file proves that the Ionescu–Wainger Fourier multiplier `iwOpSet A Φ` attached to a
finite set `A ⊆ ℝ/ℤ` of arithmetic frequencies has operator norm at most the sup norm `C` of
the symbol `Φ`, as soon as the frequencies in `A` are *non-aliasing* at scale `k` and `Φ` is
supported in the image of the frequency arc `ℝ_{≤k}` of the dual group.

The mathematics is elementary: non-aliasing says exactly that the translates `α + ℝ_{≤k}`,
`α ∈ A`, are pairwise disjoint in `ℝ/ℤ`, so at every frequency `ξ` at most one of the terms
`Φ (ξ - α)` of `iwSymbolSet A Φ ξ` is nonzero.  Hence `‖iwSymbolSet A Φ ξ‖ ≤ C` pointwise, and
the symbol is bounded by `C` in `L^∞`, which bounds the norm of the multiplier by `C`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- The Ionescu–Wainger symbol `iwSymbolSet A Φ` is bounded by the sup norm `C` of `Φ`,
provided the frequencies `A` are non-aliasing at scale `k` and `Φ` is supported in the image
of `ℝ_{≤k}`.  Indeed the arcs `α + ℝ_{≤k}` are then pairwise disjoint, so for a fixed `ξ`
at most one of the terms `Φ (ξ - α)`, `α ∈ A`, can be nonzero. -/
theorem norm_iwSymbolSet_le_of_nonAliasing {k : ℤ} {A : Finset Circle} (hA : NonAliasing k A)
    {Φ : Circle → ℂ} (hΦ : SupportedInArc k Φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖Φ ξ‖ ≤ C) :
    ∀ ξ, ‖iwSymbolSet A Φ ξ‖ ≤ C := by
  intro ξ
  by_cases hx : ∃ α ∈ A, Φ (ξ - α) ≠ 0
  · obtain ⟨α₀, hα₀, hne⟩ := hx
    -- Every other term of the sum vanishes, by non-aliasing.
    have key : ∀ β ∈ A, β ≠ α₀ → Φ (ξ - β) = 0 := by
      intro β hβ hneβ
      by_contra hβ0
      obtain ⟨θ, hθ, hθeq⟩ := hΦ (ξ - α₀) hne
      obtain ⟨θ', hθ', hθ'eq⟩ := hΦ (ξ - β) hβ0
      have heq : α₀ + (θ : Circle) = β + (θ' : Circle) := by
        rw [hθeq, hθ'eq]
        abel
      exact hneβ (hA α₀ hα₀ β hβ θ hθ θ' hθ' heq).1.symm
    have hsum : iwSymbolSet A Φ ξ = Φ (ξ - α₀) := by
      rw [iwSymbolSet_apply]
      exact Finset.sum_eq_single_of_mem α₀ hα₀ key
    rw [hsum]
    exact hC _
  · -- All terms vanish.
    have hz : ∀ α ∈ A, Φ (ξ - α) = 0 := by
      intro α hα
      by_contra h'
      exact hx ⟨α, hα, h'⟩
    rw [iwSymbolSet_apply, Finset.sum_eq_zero hz, norm_zero]
    exact hC0

theorem norm_iwOpSet_le {k : ℤ} {A : Finset Circle} (hA : NonAliasing k A)
    {Φ : Circle → ℂ} (hΦ : SupportedInArc k Φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖Φ ξ‖ ≤ C)
    (h : MeasureTheory.MemLp (iwSymbolSet A Φ) ⊤ circleMeasure) :
    ‖iwOpSet A Φ h‖ ≤ C := by
  refine norm_multiplierOf_le h hC0 ?_
  rw [eLpNorm_exponent_top (hf := by pw_aesm), eLpNormEssSup_eq_essSup_enorm]
  refine essSup_le_of_ae_le (ENNReal.ofReal C) (ae_of_all _ fun ξ => ?_)
  rw [ENNReal.ofReal, enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC0]
  exact norm_iwSymbolSet_le_of_nonAliasing hA hΦ hC0 hC ξ

end Work.Analysis.IonescuWainger
