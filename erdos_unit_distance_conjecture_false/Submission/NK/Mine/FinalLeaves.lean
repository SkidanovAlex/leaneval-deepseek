import Submission.NK.Indecomposed.All
import Submission.NK.Mine.ReducedLocalInputs
import Submission.NK.UniverseWeakNU.All

/-!
# The endgame from the final leaf list

This is the sharpest assembly of the Neukirch–Uchida theorem currently on disk.  It combines

* `NK.Indecomposed.preservesDecompositionGroups_of_hasseAt` — input (a) of CoNF (12.1.9) from, at
  every finite prime, the Hasse catalogue `NK.HasseTwist.Sha2Input`, the rank data
  `NK.Indecomposed.RankData` (the local Brauer cardinalities + Neukirch's surjectivity (9.2.1)) and
  the local reconstruction `NK.Indecomposed.LocalReconstruction` (Korollar 1 + the finishing
  step);
* `NK.Mine.localGaloisInputsTop_of_coreData` — the corrected local bundle of block (ii) from
  `NK.LocalStructure.TowerRankCore` and local class field theory
  (`NK.LocalCFT.ArtinReciprocity`);
* the *proved* arithmetic fields of the place correspondence
  (`NK.Mine.residueChar_preserved_of_topInputs`, `NK.Mine.localDegree_preserved_of_topInputs`),
  the *proved* homeomorphy of the local correspondence, and the *proved* uniqueness half;
* `NK.ReconstructField.LevelIsoInput ϕ he` — the level-wise weak Neukirch–Uchida input.

Nothing else occurs.  Note that `LocalH2Input` no longer appears: it is *derived* from the rank data
(`NK.Indecomposed.localH2Input_of_rankData`), and the residue characteristic `p` of block (ii) is
pinned to `ringChar (ResidueField (𝔭.adicCompletionIntegers K))` (a prime, by
`NK.Mine.prime_ringChar_residueField_adicCompletion`), so neither `CharP` nor the openness of
index-`p` subgroups is a hypothesis.
-/

namespace NK.Mine

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the final leaf list.** -/
theorem neukirch_uchida_of_finalLeaves
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
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
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have h := NK.Indecomposed.preservesDecompositionGroups_of_hasseAt ϕ he hB₁ hB₂
  have k₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p := by
    intro 𝔭
    have hp : (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))).Prime :=
      prime_ringChar_residueField_adicCompletion 𝔭
    have hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) :=
      charP_ringChar_residueField_adicCompletion 𝔭
    exact ⟨_, hp, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hres,
      localGaloisInputsTop_of_coreData 𝔭 hp hres (k₁ 𝔭).1 (k₁ 𝔭).2
        (fun H hH hN => isOpen_of_index_prime_of_towerRankCorePoly 𝔭 (k₁ 𝔭).1 hH hN)⟩
  have k₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q := by
    intro 𝔮
    have hq : (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))).Prime :=
      prime_ringChar_residueField_adicCompletion 𝔮
    have hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) :=
      charP_ringChar_residueField_adicCompletion 𝔮
    exact ⟨_, hq, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hq hres,
      localGaloisInputsTop_of_coreData 𝔮 hq hres (k₂ 𝔮).1 (k₂ 𝔮).2
        (fun H hH hN => isOpen_of_index_prime_of_towerRankCorePoly 𝔮 (k₂ 𝔮).1 hH hN)⟩
  exact neukirch_uchida_of_decompositionGroups ϕ he h
    (residueChar_preserved_of_topInputs ϕ h k₁' k₂')
    (localDegree_preserved_of_topInputs ϕ he h k₁' k₂') hlev


/-! ## The theorem from the leaves in their final form

`NK.UniverseWeakNU.levelIsoInput_of_chebotarev_universePoly` supplies the endgame's level input
`NK.ReconstructField.LevelIsoInput ϕ he` from

* `NK.UchidaKummer.IsUchidaModuleData 2` (Uchida's Kummer-theoretic module data, arXiv:2601.01251
  §6) and
* `NK.WeakNU.ChebotarevFrobeniusInput` (Čebotarev's density theorem in the existence form),

at *arbitrary* universes for the four fields (`Submission/Work/UniverseWeakNU/`, session 27): the
module data is only evaluated at the single common field `L = ↥N` inside an algebraically closed
field of the bottom universe, so the two inputs stay at `Type 0` while the fields live anywhere.
`NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian` reduces the Čebotarev input further to
the *abelian* case (`NK.ChebotarevGeneral.AbelianChebotarevDensity`, equivalently the Hecke input
`NK.Chebotarev.AbelianLFunctions` of `Submission/Work/HeckeL/`, which the global Artin reciprocity
law supplies). -/

section AllLeaves

variable {k₁ k₂ k₁' k₂' : Type u} [Field k₁] [Field k₂] [Field k₁'] [Field k₂']
  [NumberField k₁] [NumberField k₂] [Algebra k₁ k₁'] [Algebra k₂ k₂']
  [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the complete leaf list.** -/
theorem neukirch_uchida_of_allLeaves
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.Indecomposed.RankData p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.Indecomposed.LocalReconstruction p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.Indecomposed.RankData p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.Indecomposed.LocalReconstruction p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)))
    (k₁i : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      NK.LocalStructure.TowerRankCore k₁ 𝔭 (SeparableClosure (𝔭.adicCompletion k₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion k₁)
        (SeparableClosure (𝔭.adicCompletion k₁))))
    (k₂i : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      NK.LocalStructure.TowerRankCore k₂ 𝔮 (SeparableClosure (𝔮.adicCompletion k₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion k₂)
        (SeparableClosure (𝔮.adicCompletion k₂))))
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : NK.WeakNU.ChebotarevFrobeniusInput) :
    ∃! σ : k₂' ≃+* k₁',
      Submission.NeukirchUchida.MapsBase (algebraMap k₁ k₁') (algebraMap k₂ k₂') σ ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_finalLeaves ϕ he hB₁ hB₂ k₁i k₂i
    (NK.UniverseWeakNU.levelIsoInput_of_chebotarev_universePoly hU hC ϕ he)

end AllLeaves

end NK.Mine

