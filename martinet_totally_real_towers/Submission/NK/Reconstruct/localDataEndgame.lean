import Submission.NK.Reconstruct.endgameOfInputs
import Submission.NK.Mine.PlaceCorrespondenceArithmetic

/-!
# The Neukirch–Uchida theorem from the local leaf inputs

This module composes the σ-producing step of `Submission/Work/Reconstruct/endgameOfInputs.lean`
with the construction of the local correspondence (a) from the *local* leaf inputs
(`Submission/Work/Mine/PlaceCorrespondenceArithmetic.lean`,
`NK.Mine.localCorrespondence_of_localData`).

The result is the Neukirch–Uchida theorem (CoNF XII Theorem 12.2.1, unique existence of the inducing
field isomorphism, in exactly the predicate of the challenge statement) from

1. the local Brauer data `NK.BrauerHasse.LocalH2Input`, `NK.BrauerHasse.Sha2Vanishing` and
   `NK.BrauerHasse.LocalDecompositionCriterion` at every finite prime of both fields — CoNF
   (12.1.9) "if", the deliverable of `Submission/Work/BrauerHasse/`;
2. the local structure theory of the completions, `NK.LocalInputs.LocalFieldInputs` and
   `NK.LocalInputs.LocalGaloisInputs` at every finite prime — `Submission/Work/LocalInputs/`;
3. Uchida's weak theorem, in the form `NK.UchidaKummer.IsWeakUchida 2`, or concretely
   `NK.UchidaKummer.IsUchidaModuleData 2` + `NK.UchidaKummer.PerlisGassmannInput`;
4. Artin reciprocity, `NK.Chebotarev.ArtinReciprocityInput` at every finite Galois level (or, in
   the weaker form, the Čebotarev input `NK.Reconstruct.ChebotarevInput k₁ k₁'`).

Compared with `NK.Mine.exists_sigma_of_localData` (the assembly in
`Submission/Work/Mine/PlaceCorrespondenceArithmetic.lean`), the reconstruction input `hd` — a field
isomorphism of the separable closures realizing the place map, which is *equivalent* to the
conclusion (`NK.Reconstruct.exists_conjugates_iff_exists_realizesPlaceMap`) — is **replaced by**
items 3 and 4, and the Frobenius/local-residue inputs `PlaceLevelBridge` and `TameDataAtPlaces` are
not needed at all (the Frobenius correspondence is *derived* on this route from the level prime
identification).
-/

set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

section

variable {k₁ k₂ k₁' k₂' : Type} [Field k₁] [Field k₂] [Field k₁'] [Field k₂']
  [NumberField k₁] [NumberField k₂] [Algebra k₁ k₁'] [Algebra k₂ k₂']
  [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']

/-- **Neukirch–Uchida (CoNF XII Theorem 12.2.1) from the local leaf inputs and the weak
Neukirch–Uchida theorem.**

The hypotheses are the local Brauer data `hB₁`, `hB₂` (at the finite primes of `k₁`, `k₂`), the local
structure theory `hloc₁`, `hloc₂` of the completions, Uchida's weak theorem `hW` and the Čebotarev density
input `hc`.  The place correspondence (a) is *constructed* from the local data by
`NK.Mine.localCorrespondence_of_localData`; the base-level prime identification, the Frobenius
correspondence, the Kummer input of the differentiation lemma, the realization of the place
correspondence and the uniqueness half are all *proved*. -/
theorem existsUnique_neukirchUchidaOfLocalData
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.BrauerHasse.Sha2Vanishing p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.BrauerHasse.Sha2Vanishing p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)))
    (hloc₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs k₁ 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs k₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion k₁)) p)
    (hloc₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs k₂ 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs k₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion k₂)) q)
    (hW : NK.UchidaKummer.IsWeakUchida 2) (hc : ChebotarevInput k₁ k₁') :
    ∃! σ : k₂' ≃+* k₁',
      (algebraMap k₂ k₂').range.map σ.toRingHom = (algebraMap k₁ k₁').range ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfLocalCorrespondence ϕ hϕ
    (NK.Mine.localCorrespondence_of_localData ϕ hϕ hB₁ hB₂ hloc₁ hloc₂)
    (NK.ReconstructField.levelIsoInput_of_isWeakUchida hW ϕ hϕ) hc

/-- **Neukirch–Uchida (CoNF XII Theorem 12.2.1) from the local leaf inputs, Uchida's module data and
Artin reciprocity.**

This is `NK.Reconstruct.existsUnique_neukirchUchidaOfLocalData` with Uchida's weak theorem supplied
from `NK.UchidaKummer.IsUchidaModuleData 2` and `NK.UchidaKummer.PerlisGassmannInput`
(`NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis`) and the Čebotarev input
discharged from `NK.Chebotarev.ArtinReciprocityInput`
(`NK.Reconstruct.chebotarevInput_of_artinReciprocity`).

The hypotheses are therefore exactly four *named classical inputs*:

* the local Brauer data (CoNF (12.1.9) "if"; `Submission/Work/BrauerHasse/`),
* the local structure theory of the completions (`Submission/Work/LocalInputs/`),
* `IsUchidaModuleData 2` and `PerlisGassmannInput` (Uchida's §6; `Submission/Work/UchidaKummer/`),
* Artin reciprocity at every finite Galois level (`Submission/Work/Chebotarev/`,
  `Submission/Work/GlobalCFT/`).

No hypothesis presupposes the field isomorphism `σ`, the realization of the place correspondence,
the Frobenius correspondence or the rigidity of the place system. -/
theorem existsUnique_neukirchUchidaOfLocalDataAndSiblingInputs
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.BrauerHasse.Sha2Vanishing p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.BrauerHasse.Sha2Vanishing p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)))
    (hloc₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs k₁ 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs k₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion k₁)) p)
    (hloc₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs k₂ 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs k₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion k₂)) q)
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput)
    (hA : ∀ (L : IntermediateField k₁ k₁') [FiniteDimensional k₁ L] [Normal k₁ L]
      [NumberField ↥L] [IsGalois k₁ ↥L], NK.Chebotarev.ArtinReciprocityInput k₁ ↥L) :
    ∃! σ : k₂' ≃+* k₁',
      (algebraMap k₂ k₂').range.map σ.toRingHom = (algebraMap k₁ k₁').range ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfLocalData ϕ hϕ hB₁ hB₂ hloc₁ hloc₂
    (isWeakUchida_two_of_uchidaModuleData_and_perlis hU hP)
    (chebotarevInput_of_artinReciprocity hA)

end

end NK.Reconstruct
