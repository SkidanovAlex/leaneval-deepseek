import Submission.NK.BrauerTwist.All
import Submission.NK.Mine.TopPlaceCorrespondence
import Submission.NK.Mine.NeukirchUchidaOfLocalCorrespondence

/-!
# Neukirch–Uchida from the corrected leaves

This is the endgame with **every local input in its corrected form**:

* `NK.BrauerTwist.LocalH2Input`, `NK.BrauerTwist.Sha2Vanishing` and
  `NK.BrauerTwist.LocalDecompositionCriterion` at every finite prime (block (i)); the assembly is
  `NK.BrauerTwist.preservesDecompositionGroups_of_localGalois`.  (`NK.BrauerTwist.Sha2Vanishing`
  itself is proved from the audited catalogue `NK.HasseTwist.Sha2Input` by
  `NK.HasseTwist.sha2Vanishing`, whose module cannot be co-imported with `PTorsionTop` because of
  the duplicate commons declaration recorded in `ROADMAP.md`; the assembly below therefore takes it
  as a hypothesis.  See the note at the end of the file.)
* `NK.PTorsionTop.LocalGaloisInputsTop` at every finite prime (block (ii)): the corrected local
  structure bundle, in which the `p`-torsion field is *derived* from local reciprocity
  (`Submission/Work/PTorsionTop/`) instead of assigned through the defective abstract abelianisation;
* (nothing else: the homeomorphy of the induced local isomorphism is the *theorem*
  `NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map`, used inside
  `NK.Mine.localDegree_preserved_of_topInputs`).
* `NK.ReconstructField.LevelIsoInput ϕ he` (the level-wise weak Neukirch–Uchida input, a
  consequence of `NK.UchidaKummer.IsWeakUchida`).

The local Frobenius correspondence (input (B)) and the Jarden–Ritter place rigidity do **not** occur.
-/

namespace NK.Mine

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

theorem neukirch_uchida_of_topData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have h := NK.BrauerTwist.preservesDecompositionGroups_of_localGalois ϕ he hB₁ hB₂
  have k₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p := by
    intro 𝔭
    obtain ⟨p, hp, hres, hG⟩ := k₁ 𝔭
    exact ⟨p, hp, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hres, hG⟩
  have k₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q := by
    intro 𝔮
    obtain ⟨q, hq, hres, hG⟩ := k₂ 𝔮
    exact ⟨q, hq, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hq hres, hG⟩
  exact neukirch_uchida_of_decompositionGroups ϕ he h
    (residueChar_preserved_of_topInputs ϕ h k₁' k₂')
    (localDegree_preserved_of_topInputs ϕ he h k₁' k₂') hlev

end NK.Mine
