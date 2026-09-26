import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- If two decompositions `τ ↦ A τ + τ * B τ` of a function agree, with
`A` and `B` both `1`-periodic, then the decompositions coincide. -/
theorem PeriodicAddSmul {A₁ B₁ A₂ B₂ : ℂ → ℂ}
    (hA₁ : ∀ τ : ℂ, A₁ (τ + 1) = A₁ τ) (hA₂ : ∀ τ : ℂ, A₂ (τ + 1) = A₂ τ)
    (hB₁ : ∀ τ : ℂ, B₁ (τ + 1) = B₁ τ) (hB₂ : ∀ τ : ℂ, B₂ (τ + 1) = B₂ τ)
    (h : ∀ τ : ℂ, A₁ τ + τ * B₁ τ = A₂ τ + τ * B₂ τ) :
    (∀ τ : ℂ, A₁ τ = A₂ τ) ∧ (∀ τ : ℂ, B₁ τ = B₂ τ) := by
  have hB : ∀ τ : ℂ, B₁ τ = B₂ τ := by
    intro τ
    have h1 := h τ
    have h2 := h (τ + 1)
    rw [hA₁ τ, hA₂ τ, hB₁ τ, hB₂ τ] at h2
    have e3 : τ * (B₂ τ - B₁ τ) = (τ + 1) * (B₂ τ - B₁ τ) := by
      have e1 : A₁ τ - A₂ τ = τ * (B₂ τ - B₁ τ) := by linear_combination h1
      have e2 : A₁ τ - A₂ τ = (τ + 1) * (B₂ τ - B₁ τ) := by linear_combination h2
      exact e1 ▸ e2
    linear_combination e3
  refine ⟨?_, hB⟩
  intro τ
  have h1 := h τ
  rw [hB τ] at h1
  exact add_right_cancel h1

end Work.FunctionalEquations
