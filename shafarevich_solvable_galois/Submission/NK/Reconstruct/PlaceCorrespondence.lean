import Submission.NK.Reconstruct.LevelMap
import Submission.NK.Reconstruct.Transport
import Submission.NeukirchUchida.Detection
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The σ-free (place-based) Frobenius correspondence

The *Frobenius correspondence* (input (b) of the reconstruction) has two equivalent presentations:

* the σ-free one, `FrobeniusCorrespondencePlace ϕ hϕ a`: at every finite level `L₁ ⊆ K₁'` and every
  place `A` of `K₁'` over a finite prime, `ϕ` carries the Frobenius elements at `A` (i.e. at the
  prime of `𝓞 L₁` below `A`) to the Frobenius elements at the corresponding place `a.placeMap A` at
  the corresponding level `levelMap ϕ L₁`;
* the σ-based one, `NK.Reconstruct.FrobeniusCorrespondence ϕ σ` (`Transport.lean`), used by the
  endgame of `NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence`.

This file provides the σ-free form and the passage

`FrobeniusCorrespondencePlace ϕ hϕ a` + (a realizing `σ`) ⟹ `FrobeniusCorrespondence ϕ σ`,

so that the hypothesis set of the reconstruction can be *stated* without presupposing the field
isomorphism `σ` that the reconstruction is to produce.
-/

namespace NK.Reconstruct

set_option linter.unusedVariables false

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **A separable closure of a subfield is a separable closure of every intermediate field**: if
`K'` is a separable closure of `k` then it is a separable closure of any `L` with `k ⊆ L ⊆ K'`. -/
theorem isSepClosure_level {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (L : IntermediateField k K') : IsSepClosure ↥L K' :=
  ⟨IsSepClosure.sep_closed k, inferInstance⟩

/-- **The prime of `𝓞 L` below a place of `K₁'`**, for `L ⊆ K₁'` an intermediate field with the
bound `K₁ ⊆ L`. -/
noncomputable def primeOfLevel (A : ValuationSubring K₁') (L : IntermediateField K₁ K₁')
    [NumberField ↥L] (hA : A.comap (algebraMap ↥L K₁') ≠ ⊤) : NK.Chebotarev.PrimeIdeal ↥L :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap ↥L K₁')) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top (A.comap (algebraMap ↥L K₁'))
      hA)).choose

/-- The defining property of `primeOfLevel`. -/
theorem primeOfLevel_spec (A : ValuationSubring K₁') (L : IntermediateField K₁ K₁')
    [NumberField ↥L] (hA : A.comap (algebraMap ↥L K₁') ≠ ⊤) :
    A.comap (algebraMap ↥L K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (primeOfLevel A L hA) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap ↥L K₁')) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top (A.comap (algebraMap ↥L K₁'))
      hA)).choose_spec

/-- A place of `K₁'` over a finite prime of `K₁` restricts to a proper place of every intermediate
field `L ⊇ K₁`. -/
theorem comap_level_ne_top {A : ValuationSubring K₁'}
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) (L : IntermediateField K₁ K₁') :
    A.comap (algebraMap ↥L K₁') ≠ ⊤ := by
  intro h
  apply hA
  rw [eq_top_iff]
  intro x _
  rw [ValuationSubring.mem_comap]
  have h1 : algebraMap ↥L K₁' (algebraMap K₁ ↥L x) ∈ A := by
    have hmem : algebraMap K₁ ↥L x ∈ A.comap (algebraMap ↥L K₁') := by rw [h]; trivial
    exact (ValuationSubring.mem_comap).mp hmem
  rw [IsScalarTower.algebraMap_apply K₁ ↥L K₁' x]
  exact h1

/-- **Places of `K'` over a given prime of an intermediate level**: every finite place of a finite
level `L ⊆ K'` extends to a place of `K'`. -/
theorem exists_place_of_prime_level {k K' : Type*} [Field k] [NumberField k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (L : IntermediateField k K') [NumberField ↥L]
    (P : NK.Chebotarev.PrimeIdeal ↥L) :
    ∃ A : ValuationSubring K', A.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P := by
  haveI : IsSepClosure ↥L K' := isSepClosure_level L
  obtain ⟨A, hA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := ↥L) (K' := K') P
  exact ⟨A, hA⟩

/-- **The σ-free Frobenius correspondence** (input (b)).

For every intermediate field `L ⊆ K₁'` (finite, normal, a number field), every place `A` of `K₁'`
over a finite prime of `K₁`, and every `g : Gal(K₁'/K₁)` which is a Frobenius element at the prime
of `𝓞 L` below `A`, the element `ϕ g` is a Frobenius element at the prime of the corresponding level
`levelMap ϕ L` below the corresponding place `a.placeMap A`.

This is the form of Shimizu's Lemma 2.1.5 / CoNF (12.1.9)+§12.2 that does not presuppose the
realizing field isomorphism `σ`. -/
def FrobeniusCorrespondencePlace (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : LocalCorrespondence ϕ) : Prop :=
  ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [NumberField ↥(levelMap ϕ L)] [Normal K₂ (levelMap ϕ L)]
    (A : FinitePlaceOf K₁ K₁') (g : Gal(K₁'/K₁)),
    NK.Chebotarev.IsFrobAt (primeOfLevel A.1 L (comap_level_ne_top A.2 L))
      (AlgEquiv.restrictNormalHom L g) →
      NK.Chebotarev.IsFrobAt
        (primeOfLevel (a.placeMap A).1 (levelMap ϕ L)
          (comap_level_ne_top (a.placeMap A).2 (levelMap ϕ L)))
        (AlgEquiv.restrictNormalHom (levelMap ϕ L) (ϕ g))

/-- **The level correspondences of `ϕ` and of `σ` agree**: the image of a level under the
correspondence of `ϕ` is the level corresponding to it under `σ`.  In the classical reconstruction
this follows from the realization of the place correspondence together with Čebotarev (the two
correspondences preserve the set of completely split places, which determines the level); it is
recorded as a hypothesis here because only this consequence is used. -/
def AgreesOnLevels (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) : Prop :=
  ∀ (L : IntermediateField K₂ K₂') [FiniteDimensional K₂ L] [Normal K₂ L] [NumberField ↥L],
    levelMap ϕ (sigmaLevel σ hσ L) = L

end NK.Reconstruct
