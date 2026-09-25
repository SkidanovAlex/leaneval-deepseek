import Mathlib
import Submission.NK.TameStructureDeep.Tame.PowClassDeps
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv

namespace NK.TameStructureDeep.Tame

/-- The residue of the image of an integral element under the map of adic completions lies in the
image of the residue field of the base, which has `Nat.card κ₁` elements; hence raising it to the
`Nat.card κ₁`-th power fixes it. -/
theorem residue_adicCompletionMap_pow_card_eq_self
    {L₁ : Type*} [Field L₁] [NumberField L₁] {L₂ : Type*} [Field L₂] [NumberField L₂]
    [Algebra L₁ L₂] [FiniteDimensional L₁ L₂]
    (𝔮₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (𝔮₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (h₂ : 𝔮₂.asIdeal.LiesOver 𝔮₁.asIdeal)
    (he₂ : 𝔮₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) = 1) :
    ∀ y : 𝔮₁.adicCompletionIntegers L₁,
      (IsLocalRing.residue (𝔮₂.adicCompletionIntegers L₂)
        (⟨Commons.RingTheory.Henselian.adicCompletionMap 𝔮₁ 𝔮₂ h₂
            (y : 𝔮₁.adicCompletion L₁),
          Commons.RingTheory.Henselian.adicCompletionMap_mem_integers 𝔮₁ 𝔮₂ h₂ y.2⟩ :
          𝔮₂.adicCompletionIntegers L₂))
        ^ (Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁))) =
      IsLocalRing.residue (𝔮₂.adicCompletionIntegers L₂)
        (⟨Commons.RingTheory.Henselian.adicCompletionMap 𝔮₁ 𝔮₂ h₂
            (y : 𝔮₁.adicCompletion L₁),
          Commons.RingTheory.Henselian.adicCompletionMap_mem_integers 𝔮₁ 𝔮₂ h₂ y.2⟩ :
          𝔮₂.adicCompletionIntegers L₂) := by
  intro y
  -- the residue field of `𝔮₁.adicCompletionIntegers L₁` is finite
  haveI hfin : Finite (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L₁ 𝔮₁
  haveI : Fintype (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) := Fintype.ofFinite _
  -- the residue of the image is the image, under the natural map of residue fields, of the
  -- residue of the original element
  have hkey : IsLocalRing.residue (𝔮₂.adicCompletionIntegers L₂)
        (⟨Commons.RingTheory.Henselian.adicCompletionMap 𝔮₁ 𝔮₂ h₂
            (y : 𝔮₁.adicCompletion L₁),
          Commons.RingTheory.Henselian.adicCompletionMap_mem_integers 𝔮₁ 𝔮₂ h₂ y.2⟩ :
          𝔮₂.adicCompletionIntegers L₂) =
      Commons.NumberTheory.NumberField.Completion.natResidueMap 𝔮₁ 𝔮₂ h₂
        (IsLocalRing.residue (𝔮₁.adicCompletionIntegers L₁) y) :=
    (Commons.NumberTheory.NumberField.Completion.natResidueMap_residue 𝔮₁ 𝔮₂ h₂ y).symm
  rw [hkey, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

end NK.TameStructureDeep.Tame
