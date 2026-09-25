import Mathlib
import Submission.NK.Reconstruct.Basic
import Submission.NK.Reconstruct.exists_placeCongr
import Submission.NK.Reconstruct.GammaObject

/-!
# The transport of the local correspondence along an isomorphism of separable closures

Let `K₁`, `K₂` be number fields, and let `K₁'`, `K₂'` be separable closures of `K₁`, `K₂`.  The
reconstruction step of Neukirch–Uchida is phrased in the two-closure setting, but Shimizu's
abelianised route (§4 of arXiv:2009.10431, cf. §18 of the README of this area) works inside *one*
separable closure `Ω` of `K₂` which simultaneously plays the role of `K₂'`.  The passage from the
pair `(K₂', Ω)` of separable closures of `K₂` to the single closure `Ω` is an isomorphism
`e : K₂' ≃ₐ[K₂] Ω`, and conjugation by `e` identifies the two absolute Galois groups:
`ψ := e (·) e⁻¹ ∘ ϕ` is an isomorphism `Gal(K₁'/K₁) ≃* Gal(Ω/K₂)`.

This file proves that a local correspondence for `ϕ` transports to one for any such conjugate:

`NK.Reconstruct.exists_localCorrespondence_transport` — if `a : LocalCorrespondence ϕ` is the
local correspondence of `ϕ` (CoNF XII (12.1.9)) and `ψ` is the conjugate of `ϕ` by `e`, then there
is a local correspondence for `ψ`.

The construction is the evident one: a place of `K₁'` over a finite prime of `K₁` is sent to the
place of `Ω` obtained by transporting its image under `a.placeMap` along `e`
(`NK.Reconstruct.placeCongr`, the place bijection induced by `e`, in the direction
`FinitePlaceOf K₂ K₂' ≃ FinitePlaceOf K₂ Ω`).  The three structural fields of
`LocalCorrespondence` are then the corresponding compatibility statements:

* Galois equivariance of the place map follows from the equivariance of `placeCongr`
  (`NK.Reconstruct.placeCongr_smul`) and the fact that the conjugating isomorphism
  `algEquivConjHom e.symm : Gal(Ω/K₂) →* Gal(K₂'/K₂)` is inverse to `algEquivConjHom e`
  (`algEquivConjHom_symm_apply_apply`);
* compatibility with decomposition groups follows from `NK.Reconstruct.placeCongr_decomp`
  together with `Subgroup.map_map`;
* the induced bijection of primes, the residue characteristic and the local degree are unchanged,
  because *the prime below a place does not change when the place is transported along `e`*
  (`primeOf_placeCongr_symm`: both traces on `K₂` are computed from the same `e.symm`-pullback).

Everything is elementary bookkeeping: no new mathematical input is consumed.
-/

namespace NK.Reconstruct

open scoped Pointwise

/-! ## Conjugation by an algebra isomorphism -/

section ConjHelpers

variable {F : Type*} [Field F] {X : Type*} [Field X] {Y : Type*} [Field Y]
  [Algebra F X] [Algebra F Y]

/-- **Conjugation by `e.symm` undoes conjugation by `e`**: the conjugation isomorphism
`algEquivConjHom e : Gal(X/F) →* Gal(Y/F)` and its counterpart `algEquivConjHom e.symm` for the
inverse isomorphism are mutually inverse. -/
lemma algEquivConjHom_symm_apply_apply (e : X ≃ₐ[F] Y) (τ : X ≃ₐ[F] X) :
    algEquivConjHom e.symm (algEquivConjHom e τ) = τ := by
  ext x
  simp [algEquivConjHom, AlgEquiv.trans_apply]

/-- The same statement in the other order: conjugation by `e` undoes conjugation by `e.symm`. -/
lemma algEquivConjHom_apply_apply_symm (e : X ≃ₐ[F] Y) (σ : Y ≃ₐ[F] Y) :
    algEquivConjHom e (algEquivConjHom e.symm σ) = σ := by
  ext y
  simp [algEquivConjHom, AlgEquiv.trans_apply]

/-- The monoid-homomorphism form of `algEquivConjHom_apply_apply_symm`. -/
lemma algEquivConjHom_comp_symm_comp (e : X ≃ₐ[F] Y) :
    (algEquivConjHom e).comp (algEquivConjHom e.symm) = MonoidHom.id (Y ≃ₐ[F] Y) := by
  ext σ y
  simp [algEquivConjHom, AlgEquiv.trans_apply]

end ConjHelpers

/-! ## The place bijection of the inverse direction -/

section PlaceTransport

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] {Ω : Type*} [Field Ω]
  [Algebra K K'] [Algebra K Ω] [IsSepClosure K K'] [IsSepClosure K Ω]

/-- The underlying place of the transported place `(placeCongr e).symm B` is the pullback of `B`
along `e.symm`. -/
lemma coe_placeCongr_symm (e : K' ≃ₐ[K] Ω) (B : FinitePlaceOf K K') :
    ((placeCongr e).symm B).1 = B.1.comap (e.symm : Ω →+* K') := rfl

/-- **The inverse direction of the equivariance of the place bijection**: the place map
`(placeCongr e).symm : FinitePlaceOf K K' ≃ FinitePlaceOf K Ω` is equivariant for the two Galois
actions, through the conjugation isomorphism `algEquivConjHom e.symm`.

(Spelled out with `placeSmul₂` in the form in which the fields of `LocalCorrespondence` consume
it.) -/
lemma placeCongr_symm_placeSmul₂ (e : K' ≃ₐ[K] Ω) (g : Gal(Ω/K)) (B : FinitePlaceOf K K') :
    (placeCongr e).symm
        (placeSmul₂ (K₂ := K) (K₂' := K') (algEquivConjHom e.symm g) B) =
      placeSmul₂ (K₂ := K) (K₂' := Ω) g ((placeCongr e).symm B) := by
  have h : (placeCongr e).symm
        (placeSmul (K₁ := K) (K₁' := K') (algEquivConjHom e.symm g) B) =
      placeSmul (K₁ := K) (K₁' := Ω) g ((placeCongr e).symm B) := by
    rw [Equiv.symm_apply_eq]
    show placeSmul (K₁ := K) (K₁' := K') (algEquivConjHom e.symm g) B =
      placeCongr e (placeSmul (K₁ := K) (K₁' := Ω) g ((placeCongr e).symm B))
    have h2 := placeCongr_smul e ((placeCongr e).symm B) g
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm
  exact h

/-- **The prime below a place is unchanged by the transport of places along `e`.**  The transported
place `(placeCongr e).symm B` is the pullback of `B` along `e.symm`, so its trace on the base field
`K` is the same as that of `B`. -/
lemma primeOf_placeCongr_symm (e : K' ≃ₐ[K] Ω) (B : FinitePlaceOf K K') :
    Submission.NeukirchUchida.primeOf ((placeCongr e).symm B).1 ((placeCongr e).symm B).2 =
      Submission.NeukirchUchida.primeOf B.1 B.2 := by
  have hval : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (Submission.NeukirchUchida.primeOf ((placeCongr e).symm B).1
          ((placeCongr e).symm B).2) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (Submission.NeukirchUchida.primeOf B.1 B.2) := by
    rw [← Submission.NeukirchUchida.primeOf_spec ((placeCongr e).symm B).1
          ((placeCongr e).symm B).2,
        ← Submission.NeukirchUchida.primeOf_spec B.1 B.2]
    show (((placeCongr e).symm B).1.comap (algebraMap K Ω)) = B.1.comap (algebraMap K K')
    rw [coe_placeCongr_symm, ValuationSubring.comap_comap, symm_comp_algebraMap_eq e]
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hval

end PlaceTransport

/-! ## The transport of the local correspondence -/

theorem exists_localCorrespondence_transport {K₁ K₂ K₁' K₂' Ω : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Field Ω] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [Algebra K₂ Ω] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [IsSepClosure K₂ Ω]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (a : LocalCorrespondence ϕ) (e : K₂' ≃ₐ[K₂] Ω)
    (ψ : Gal(K₁'/K₁) ≃* Gal(Ω/K₂))
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g)) :
    Nonempty (LocalCorrespondence ψ) := by
  classical
  -- `ψ` is the composite of `ϕ` with the conjugation isomorphism induced by `e`
  have hψhom : (ψ : Gal(K₁'/K₁) →* Gal(Ω/K₂)) =
      (algEquivConjHom e).comp (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
  MonoidHom.ext fun g => hψ g
  -- the inverse conjugation carries `ψ g` back to `ϕ g`
  have hplace : ∀ g : Gal(K₁'/K₁), algEquivConjHom e.symm (ψ g) = ϕ g := by
    intro g
    rw [hψ g]
    exact algEquivConjHom_symm_apply_apply e (ϕ g)
  -- the prime below a place is unchanged by the transport along `e`
  have hprime : ∀ A : FinitePlaceOf K₁ K₁',
      Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2 =
        Submission.NeukirchUchida.primeOf (a.placeMap A).1 (a.placeMap A).2 :=
    fun A => primeOf_placeCongr_symm (K := K₂) (K' := K₂') (Ω := Ω) e (a.placeMap A)
  refine ⟨{ placeMap := a.placeMap.trans (placeCongr e).symm
            map_smul := ?_
            map_decomp := ?_
            primeMap := a.primeMap
            primeMap_spec := ?_
            residueChar := ?_
            localDegree := ?_ }⟩
  · intro g A
    show (placeCongr e).symm (a.placeMap (placeSmul g A)) =
      placeSmul₂ (K₂ := K₂) (K₂' := Ω) (ψ g) ((placeCongr e).symm (a.placeMap A))
    rw [a.map_smul g A]
    have h := placeCongr_symm_placeSmul₂ (K := K₂) (K' := K₂') (Ω := Ω) e (ψ g) (a.placeMap A)
    rw [hplace g] at h
    exact h
  · intro A
    show (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1).map
          (ψ : Gal(K₁'/K₁) →* Gal(Ω/K₂)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := Ω)
          ((placeCongr e).symm (a.placeMap A)).1
    rw [hψhom]
    rw [← Subgroup.map_map]
    rw [a.map_decomp A]
    have hpc := placeCongr_decomp (K := K₂) (K' := K₂') (Ω := Ω) e
      ((placeCongr e).symm (a.placeMap A))
    rw [Equiv.apply_symm_apply] at hpc
    rw [hpc]
    rw [Subgroup.map_map]
    rw [algEquivConjHom_comp_symm_comp e]
    rw [Subgroup.map_id]
  · intro A
    show a.primeMap (Submission.NeukirchUchida.primeOf A.1 A.2) =
      Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
        ((placeCongr e).symm (a.placeMap A)).2
    rw [hprime A]
    exact a.primeMap_spec A
  · intro A ℓ h
    show CharP (NumberField.RingOfIntegers K₂ ⧸
        (Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2).asIdeal) ℓ
    rw [hprime A]
    exact a.residueChar A ℓ h
  · intro A
    show ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ) *
        ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ) =
      ((Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2).asIdeal.inertiaDeg ℤ) *
        ((Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2).asIdeal.ramificationIdx ℤ)
    rw [hprime A]
    exact a.localDegree A

end NK.Reconstruct
