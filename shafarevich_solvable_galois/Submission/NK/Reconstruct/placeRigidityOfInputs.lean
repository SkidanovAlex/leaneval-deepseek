import Submission.NK.Reconstruct.endgameOfInputs
import Submission.NK.Reconstruct.PlaceRigidity
import Submission.NK.Mine.PlaceCorrespondenceArithmetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Jarden–Ritter rigidity from the σ-producing step: the case `K₁ = K₂`

`NK.Reconstruct.PlaceRigidity K K'` is the rigidity of the place system of `K'` over `K`: every
automorphism `ψ` of `Gal(K'/K)` which maps the family of decomposition groups of the places over
the finite primes of `K` to itself is of the form `conjHomEquiv h_c` for a field automorphism
`c : K' ≃+* K'` preserving the embedded copy of `K`.  It is the input consumed by
`NK.ReconstructField.exists_sigma_of_weak_and_placeRigidity`,
`NK.UchidaKummer.exists_sigma_of_uchidaModuleData_and_perlis` and
`Submission/Work/UchidaKummer/Assembly.lean`; the *inner* form is false (§7 of the README).

This module shows that, for *continuous* `ψ`, the rigidity is a **theorem**, not an input: it is the
case `K₁ = K₂` of the σ-producing step of this area
(`NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIsoInput` with `ϕ := ψ`), whose
hypotheses are the local correspondence `LocalCorrespondence ψ` — supplied by the local leaf inputs
through `NK.Mine.localCorrespondence_of_localData` — the level-wise weak Neukirch–Uchida input (W)
— supplied by Uchida's weak theorem, i.e. `NK.UchidaKummer.IsUchidaModuleData 2` and
`NK.UchidaKummer.PerlisGassmannInput` — and the Čebotarev input.

Consequently "a place-preserving automorphism of `G_K` is induced by a field automorphism" is *not*
an independent arithmetic input of the fleet: it is a corollary of the machinery of this area.  (For
`K = ℚ` this is the classical instance of Neukirch–Uchida's Theorem 12.2.1 in the case `K₁ = K₂`.)
-/

set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

/-- **Jarden–Ritter rigidity from the σ-producing step** (the case `K₁ = K₂` of
`NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIsoInput`).

For a homeomorphic automorphism `ψ` of `Gal(K'/K)` with local correspondence `a`, the level-wise
weak Neukirch–Uchida input (W) and Čebotarev, there is a *field* automorphism `c` of `K'` preserving
the embedded copy of `K` with `ψ = conjHomEquiv h_c`. -/
theorem exists_conjHomEquiv_of_localCorrespondence {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ψ : Gal(K'/K) ≃* Gal(K'/K)) (hψ : IsHomeomorph ψ) (a : LocalCorrespondence ψ)
    (hlev : NK.ReconstructField.LevelIsoInput ψ hψ) (hc : ChebotarevInput K K') :
    ∃ (c : K' ≃+* K')
      (hc' : Submission.NeukirchUchida.MapsBase (algebraMap K K') (algebraMap K K') c),
      ψ = Submission.NeukirchUchida.conjHomEquiv hc' := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_localCorrespondence_of_levelIsoInput ψ hψ a hlev hc
  refine ⟨σ, hσ.1, MulEquiv.ext (fun g => AlgEquiv.ext (fun x => ?_))⟩
  have h := congrArg (fun (e : K' ≃+* K') => e x) (hσ.2 g)
  have hconj : (Submission.NeukirchUchida.conjHomEquiv hσ.1) g
      = Submission.NeukirchUchida.conj hσ.1 g := rfl
  rw [hconj, Submission.NeukirchUchida.conj_apply]
  simpa [RingEquiv.trans_apply] using h

/-- **Jarden–Ritter rigidity for continuous automorphisms, from Uchida's weak theorem.**

This is `NK.Reconstruct.exists_conjHomEquiv_of_localCorrespondence` with (W) supplied by Uchida's
weak theorem (`NK.UchidaKummer.IsWeakUchida 2`, from `IsUchidaModuleData 2` and
`PerlisGassmannInput`), the fields living in `Type` because those inputs do. -/
theorem exists_conjHomEquiv_of_uchidaData {K : Type} [Field K] [NumberField K]
    {K' : Type} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ψ : Gal(K'/K) ≃* Gal(K'/K)) (hψ : IsHomeomorph ψ) (a : LocalCorrespondence ψ)
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput) (hc : ChebotarevInput K K') :
    ∃ (c : K' ≃+* K')
      (hc' : Submission.NeukirchUchida.MapsBase (algebraMap K K') (algebraMap K K') c),
      ψ = Submission.NeukirchUchida.conjHomEquiv hc' :=
  exists_conjHomEquiv_of_localCorrespondence ψ hψ a
    (NK.ReconstructField.levelIsoInput_of_isWeakUchida
      (isWeakUchida_two_of_uchidaModuleData_and_perlis hU hP) ψ hψ) hc

/-- **Jarden–Ritter rigidity from the *leaf* inputs of the fleet.**

For every *homeomorphic* automorphism `ψ` of the absolute Galois group `Gal(K'/K)` of a number field
`K` which maps the family of decomposition groups of the places over the finite primes of `K` to
itself, there is a field automorphism `c : K' ≃+* K'` preserving the embedded copy of `K` with
`ψ = conjHomEquiv h_c`.

The hypotheses are exactly the leaf inputs used elsewhere in the development: the local Brauer data
`hB₁`, `hB₂` (CoNF (12.1.9) "if", `Submission/Work/BrauerHasse/`) and the local structure theory
`hloc₁`, `hloc₂` (`Submission/Work/LocalInputs/`), which construct the local correspondence `a`
through `NK.Mine.localCorrespondence_of_localData`; Uchida's module data and Perlis/Gassmann
(`Submission/Work/UchidaKummer/`); and Artin reciprocity in the form of the Čebotarev input
(`Submission/Work/Chebotarev/`). -/
theorem placeRigidity_of_localData (K : Type) [Field K] [NumberField K]
    (K' : Type) [Field K'] [Algebra K K'] [IsSepClosure K K']
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p K K'
          (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K)) ∧
        NK.BrauerHasse.Sha2Vanishing p K K'
          (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p K K'
          (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p K K'
          (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K)) ∧
        NK.BrauerHasse.Sha2Vanishing p K K'
          (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p K K'
          (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K)))
    (hloc₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs K 𝔭
          (SeparableClosure (𝔭.adicCompletion K)) p)
    (hloc₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs K 𝔮
          (SeparableClosure (𝔮.adicCompletion K)) q)
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput) (hc : ChebotarevInput K K')
    (ψ : Gal(K'/K) ≃* Gal(K'/K)) (hψ : IsHomeomorph ψ)
    (hplace : ∀ B : ValuationSubring K', B.comap (algebraMap K K') ≠ ⊤ →
      ∃ B' : ValuationSubring K', B'.comap (algebraMap K K') ≠ ⊤ ∧
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') B).map
          (ψ : Gal(K'/K) →* Gal(K'/K)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') B') :
    ∃ (c : K' ≃+* K')
      (hc' : Submission.NeukirchUchida.MapsBase (algebraMap K K') (algebraMap K K') c),
      ψ = Submission.NeukirchUchida.conjHomEquiv hc' :=
  exists_conjHomEquiv_of_uchidaData ψ hψ
    (NK.Mine.localCorrespondence_of_localData ψ hψ hB₁ hB₂ hloc₁ hloc₂) hU hP hc

/-! ## The realization input of `Submission/NeukirchUchida/Endgame.lean`, rigidity-free

The input `(d)` of `Submission.NeukirchUchida.exists_sigma_of_reconstruction` — a `MapsBase`
isomorphism of the separable closures realizing the place correspondence `a` — is supplied on the
*rigidity* route by `NK.UchidaKummer.exists_sigma_of_uchidaModuleData_and_perlis`, whose
hypotheses include `NK.Reconstruct.PlaceRigidity K₂ K₂'`.  The theorem below supplies it instead
from (a), Uchida's module data and Perlis/Gassmann, and the Čebotarev input, with **no rigidity
input**; by `NK.Reconstruct.exists_conjHomEquiv_of_uchidaData` the rigidity itself is a
consequence of these inputs in the case `K₁ = K₂`. -/

/-- **The realization input (d) of `Submission/NeukirchUchida/Endgame.lean`, from (a), Uchida's
module data, Perlis/Gassmann and Čebotarev** — without the Jarden–Ritter rigidity. -/
theorem exists_sigma_realizing_of_uchidaData {K₁ K₂ K₁' K₂' : Type} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput) (hc : ChebotarevInput K₁ K₁') :
    ∃ (σ : K₂' ≃+* K₁')
      (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ∧
        Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ⟩ :=
    exists_sigma_of_localCorrespondence_of_levelIsoInput ϕ hϕ a
      (NK.ReconstructField.levelIsoInput_of_isWeakUchida
        (isWeakUchida_two_of_uchidaModuleData_and_perlis hU hP) ϕ hϕ) hc
  exact ⟨σ, hσ.1, comap_placeMap_eq_of_conjugates a hσ, hσ⟩

end NK.Reconstruct
