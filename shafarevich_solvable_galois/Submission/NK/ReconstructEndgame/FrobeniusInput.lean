import Submission.NK.ReconstructEndgame.Main
import Submission.NK.ResidueFrob.LocalStructureInputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shimizu endgame with the Frobenius correspondence discharged

Input (iii) of the Shimizu route, the σ-free Frobenius correspondence
`NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a`, is *discharged* here by the local structure
theory at the places of the two fields: `NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData`
produces it from `NK.ResidueFrob.LocalStructureData` at every place (the reduced local input
catalogue of `Submission/Work/LocalStructure/` and `Submission/Work/TameData/`, see the README of
`Submission/Work/ResidueFrob/`).  Since the local structure data does not depend on `a`, it gives
the `∀ a` form required by `Main.lean`.

This module is imported by `Submission.NK.ReconstructEndgame.All`; it is the only module of the
chapter that depends on `Submission.NK.ResidueFrob`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.ReconstructEndgame

section FrobeniusInput

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The Frobenius correspondence of the Shimizu route, in the `∀ a` form needed by the endgame,
from the local structure theory at the places of the two fields.**

`NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData` produces
`FrobeniusCorrespondencePlace ϕ he a` for each `a` from data that does not depend on `a`, so the
quantification over `a` is immediate. -/
theorem forall_frobeniusCorrespondencePlace_of_localStructureData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B) :
    ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a :=
  fun a => NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData ϕ he a h₁ h₂

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the Shimizu route, with the Frobenius
correspondence discharged by the local structure theory at the places of the two fields.**

The remaining inputs are block (i), block (ii), a prime `ℓ` and the three rank inputs and
Čebotarev; the `ℚ`-algebra structure on `K₁'` is derived. -/
theorem neukirch_uchida_of_localStructureData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 :=
  neukirch_uchida_of_reconstructLeaves ϕ he hB₁ hB₂ k₁ k₂
    (forall_frobeniusCorrespondencePlace_of_localStructureData ϕ he h₁ h₂) ℓ hH hM hR hc

/-- **The existence half of Neukirch–Uchida** in the same shape as
`neukirch_uchida_of_localStructureData`. -/
theorem exists_sigma_of_localStructureData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
 := by
  obtain ⟨σ, hσ, _⟩ :=
    neukirch_uchida_of_localStructureData ϕ he hB₁ hB₂ k₁ k₂ h₁ h₂ ℓ hH hM hR hc
  exact ⟨σ, hσ⟩

end FrobeniusInput

end NK.ReconstructEndgame
