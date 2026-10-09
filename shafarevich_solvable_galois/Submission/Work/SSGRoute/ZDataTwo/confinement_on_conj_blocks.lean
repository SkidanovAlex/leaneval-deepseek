import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

open scoped Pointwise

/-- `IsConjPlace` is transitive (compose the conjugating elements). -/
private theorem isConjPlace_trans' {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {A B C : ValuationSubring Ω} (h₁ : SSGRoute.IsConjPlace k A B)
    (h₂ : SSGRoute.IsConjPlace k B C) : SSGRoute.IsConjPlace k A C := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩

/-- `gesKConj` is transitive (the fixing subgroup of `K` is closed under multiplication). -/
private theorem gesKConj_trans' {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {A B C : ValuationSubring Ω}
    (h₁ : Work.SSGRoute.gesKConj K A B) (h₂ : Work.SSGRoute.gesKConj K B C) :
    Work.SSGRoute.gesKConj K A C := by
  obtain ⟨τ, hτK, hτ⟩ := h₁
  obtain ⟨ρ, hρK, hρ⟩ := h₂
  exact ⟨ρ * τ, K.fixingSubgroup.mul_mem hρK hτK, by rw [mul_smul, hτ, hρ]⟩

/-- `K`-conjugacy implies `k`-conjugacy. -/
private theorem isConjPlace_of_gesKConj' {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) : SSGRoute.IsConjPlace k A B :=
  ⟨h.choose, h.choose_spec.2⟩

/-- **Confinement passes from one `K`-block to the union of its `k`-conjugate blocks.**

If a function vanishing on the inertia of every finite place `B` that is `K`-non-conjugate to all of
`T` and to `Q`, and `T` consists of places each of which is either a `k`-conjugate of an element of
`S` or a `K`-conjugate of an element of `H`, then the same vanishing holds at every finite place that
is `k`-non-conjugate to all of `S` and all of `H` and is `K`-non-conjugate to `Q`.

This is the bookkeeping step that lets a datum prescribed only on `S` and `H` (a set of
`k`-conjugacy classes) by a confinement valid on `T` (a set of `K`-classes) be used at *every*
`B` `k`-non-conjugate to `S` and `H`: a `B` that were `K`-conjugate to some `A ∈ T` would, by
transitivity of `gesKConj` along the `hTS` alternative, be `k`-conjugate to an element of `S` or of
`H`, contradicting the hypotheses. -/
theorem confinement_on_conj_blocks (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ)
    (S H T : Finset (ValuationSubring Ω)) (Q : ValuationSubring Ω)
    (hTS : ∀ A ∈ T, (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) ∨
      (∃ Q' ∈ H, Work.SSGRoute.gesKConj K Q' A))
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ B) →
      (∀ Q' ∈ H, ¬ SSGRoute.IsConjPlace k Q' B) →
      (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0 := by
  intro B hBfin hS hH hQ σ hσ hI
  refine hconf B hBfin ?_ hQ σ hσ hI
  intro A hA hgAB
  rcases hTS A hA with ⟨A₀, hA₀S, hA₀A⟩ | ⟨Q', hQ'H, hQ'A⟩
  · exact hS A₀ hA₀S (isConjPlace_trans' hA₀A (isConjPlace_of_gesKConj' hgAB))
  · exact hH Q' hQ'H (isConjPlace_of_gesKConj' (gesKConj_trans' hQ'A hgAB))

end Work.SSGRoute.ZDataTwo
