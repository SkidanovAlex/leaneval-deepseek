import Mathlib
import Submission.NK.EndgameRepair.Endgame

namespace NK.EndgameRepair

universe u

theorem neukirch_uchida_of_reconstructLeaves_corrected
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.EndgameRepair.Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  exact neukirch_uchida_of_preserves_corrected ϕ he
    (NK.Indecomposed.preservesDecompositionGroups_of_hasseAt ϕ he hB₁ hB₂)
    (fun 𝔭 => NK.ReconstructEndgame.exists_localGaloisInputsTop_of_coreData K₁ 𝔭 (k₁ 𝔭))
    (fun 𝔮 => NK.ReconstructEndgame.exists_localGaloisInputsTop_of_coreData K₂ 𝔮 (k₂ 𝔮))
    hb ℓ h45 hc

end NK.EndgameRepair
