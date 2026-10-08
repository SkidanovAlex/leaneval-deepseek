import Mathlib
import Submission.Work.BG.S02

namespace Work.BG

open OddOrder.RepresentationTheory

/-- If the sum of two distinct irreducible characters is invariant under an automorphism `σ`
of the group (i.e. `α₁ ∘ σ + α₂ ∘ σ = α₁ + α₂`), then `σ` either fixes both characters or
interchanges them.

This is the "a two-element orbit of `Irr` is either fixed pointwise or swapped" statement used
in the Gorenstein–Walter argument: the invariant sum has a unique decomposition into
irreducibles, and orthonormality of `Irr` pins that decomposition down.

Proof.  Put `βᵢ = αᵢ ∘ σ` (`ClassFunction.compHom`).  Each `βᵢ` is an irreducible character
(`IsIrreducibleCharacter.compHom_of_surjective`), and the hypothesis says `β₁ + β₂ = α₁ + α₂`.
Pairing with `α₁` and using orthonormality (`irr_cf_inner`) gives
`⟨β₁, α₁⟩ + ⟨β₂, α₁⟩ = ⟨α₁, α₁⟩ + ⟨α₂, α₁⟩ = 1 + 0 = 1`; each of the two terms is `δ`, so
exactly one of `β₁ = α₁`, `β₂ = α₁` holds.  Cancelling the common summand in `β₁ + β₂ = α₁ + α₂`
then gives the two conclusions. -/
theorem fixesOrSwapsTwoIrr {U : Type} [Group U] [Fintype U] [Invertible (Nat.card U : ℂ)]
    (σ : MulAut U) {α₁ α₂ : OddOrder.RepresentationTheory.ClassFunction U ℂ}
    (hα₁ : OddOrder.RepresentationTheory.IsIrreducibleCharacter α₁)
    (hα₂ : OddOrder.RepresentationTheory.IsIrreducibleCharacter α₂) (hne : α₁ ≠ α₂)
    (hsum : ∀ u : U, α₁ (σ u) + α₂ (σ u) = α₁ u + α₂ u) :
    ((∀ u : U, α₁ (σ u) = α₁ u) ∧ (∀ u : U, α₂ (σ u) = α₂ u)) ∨
      ((∀ u : U, α₁ (σ u) = α₂ u) ∧ (∀ u : U, α₂ (σ u) = α₁ u)) := by
  classical
  set β₁ : ClassFunction U ℂ := ClassFunction.compHom (σ : U →* U) α₁ with hβ₁def
  set β₂ : ClassFunction U ℂ := ClassFunction.compHom (σ : U →* U) α₂ with hβ₂def
  have hβ₁irr : IsIrreducibleCharacter β₁ := hα₁.compHom_of_surjective σ.surjective
  have hβ₂irr : IsIrreducibleCharacter β₂ := hα₂.compHom_of_surjective σ.surjective
  -- The invariant sum, transported to `β₁ + β₂ = α₁ + α₂`.
  have hβ : β₁ + β₂ = α₁ + α₂ := by
    apply ClassFunction.ext
    intro u
    simp only [ClassFunction.add_apply]
    rw [hβ₁def, hβ₂def, ClassFunction.compHom_apply, ClassFunction.compHom_apply]
    exact hsum u
  have e11 : ClassFunction.inner α₁ α₁ = 1 := by
    rw [irr_cf_inner hα₁ hα₁, ite_eq_left rfl]
  have e21 : ClassFunction.inner α₂ α₁ = 0 := by
    rw [irr_cf_inner hα₂ hα₁, ite_eq_right (Ne.symm hne)]
  -- Pairing the invariant identity with `α₁` shows exactly one of `β₁ = α₁`, `β₂ = α₁`.
  have hsum_inner : ClassFunction.inner β₁ α₁ + ClassFunction.inner β₂ α₁ = 1 := by
    have h1 : ClassFunction.inner (β₁ + β₂) α₁ = ClassFunction.inner (α₁ + α₂) α₁ := by rw [hβ]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_left, e11, e21, add_zero] at h1
    exact h1
  have hinner1 : ClassFunction.inner β₁ α₁ = if β₁ = α₁ then 1 else 0 := irr_cf_inner hβ₁irr hα₁
  have hinner2 : ClassFunction.inner β₂ α₁ = if β₂ = α₁ then 1 else 0 := irr_cf_inner hβ₂irr hα₁
  have hcases : β₁ = α₁ ∨ β₂ = α₁ := by
    by_cases h1 : β₁ = α₁
    · exact Or.inl h1
    · right
      by_contra h2
      rw [ite_eq_right h1] at hinner1
      rw [ite_eq_right h2] at hinner2
      rw [hinner1, hinner2] at hsum_inner
      norm_num at hsum_inner
  rcases hcases with h1 | h1
  · -- `σ` fixes `α₁`, hence also `α₂`.
    left
    have h2 : β₂ = α₂ := by
      rw [h1] at hβ
      exact add_left_cancel hβ
    refine ⟨?_, ?_⟩
    · intro u
      have hh := congrFun (congrArg (fun f : ClassFunction U ℂ => (f : U → ℂ)) h1) u
      simpa [hβ₁def] using hh
    · intro u
      have hh := congrFun (congrArg (fun f : ClassFunction U ℂ => (f : U → ℂ)) h2) u
      simpa [hβ₂def] using hh
  · -- `σ` swaps the two characters.
    right
    have h2 : β₁ = α₂ := by
      rw [h1, add_comm (α₁ : ClassFunction U ℂ) α₂] at hβ
      exact add_right_cancel hβ
    refine ⟨?_, ?_⟩
    · intro u
      have hh := congrFun (congrArg (fun f : ClassFunction U ℂ => (f : U → ℂ)) h2) u
      simpa [hβ₁def] using hh
    · intro u
      have hh := congrFun (congrArg (fun f : ClassFunction U ℂ => (f : U → ℂ)) h1) u
      simpa [hβ₂def] using hh

end Work.BG
