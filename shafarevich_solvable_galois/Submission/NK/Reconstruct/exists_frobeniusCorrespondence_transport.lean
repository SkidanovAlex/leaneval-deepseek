import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.Reconstruct.exists_localCorrespondence_transport
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
import Submission.NK.Reconstruct.isFrobAt_primeTransport_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transport of the Frobenius correspondence along an isomorphism of separable closures

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`, and let `Ω` be a further
separable closure of `K₂`.  An isomorphism `e : K₂' ≃ₐ[K₂] Ω` conjugates the isomorphism
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` into the isomorphism `ψ := e (·) e⁻¹ ∘ ϕ : Gal(K₁'/K₁) ≃* Gal(Ω/K₂)`,
and transports the local correspondence `a` of `ϕ` into the local correspondence `a'` of `ψ` whose
place map is `A ↦ (a.placeMap A).1.comap e.symm` (`NK.Reconstruct.exists_localCorrespondence_transport`).

This file proves that the *Frobenius correspondence* (`FrobeniusCorrespondencePlace`) transports
along the same data: if `b` is the Frobenius correspondence for `ϕ` and `a`, then `a'` is one for
`ψ`, i.e. at corresponding places, the Frobenius elements match.

The proof is a transport of the finite-level statement:

* the level `levelMap ψ L ⊆ Ω` of `ψ` attached to a level `L ⊆ K₁'` is the image of `levelMap ϕ L`
  under `e`, so that `e` restricts to an isomorphism of levels
  `levelConjEquiv : ↥(levelMap ϕ L) ≃+* ↥(levelMap ψ L)`;
* the restriction of `ψ g` to `levelMap ψ L` is the conjugate by this level isomorphism of the
  restriction of `ϕ g` to `levelMap ϕ L` (`restrictNormalHom_levelConjEquiv`);
* the prime of `𝓞 (levelMap ψ L)` below the transported place is the transport of the prime below
  the original place (`primeOfLevel_comap_conj`), by uniqueness of the valuation ring at a prime;
* Frobenius elements are preserved by the transport of primes along a level isomorphism
  (`NK.Reconstruct.isFrobAt_primeTransport_iff`).
-/

namespace NK.Reconstruct

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section ConjLevel

variable {K₁ K₂ K₁' K₂' Ω : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Field Ω] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [Algebra K₂ Ω]
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [IsSepClosure K₂ Ω]
  (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (e : K₂' ≃ₐ[K₂] Ω) (ψ : Gal(K₁'/K₁) ≃* Gal(Ω/K₂))

/-- Conjugation by `e`, as the map `τ ↦ e ∘ τ ∘ e⁻¹` on automorphisms of `Ω`. -/
lemma algEquivConjHom_apply_coe (τ : K₂' ≃ₐ[K₂] K₂') (y : Ω) :
    algEquivConjHom e τ y = e (τ (e.symm y)) := rfl

/-- **Membership of the image of a point of `levelMap ϕ L`.** -/
lemma mem_levelMap_conj (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    {L : IntermediateField K₁ K₁'} {x : K₂'} (hx : x ∈ levelMap ϕ L) :
    e x ∈ levelMap ψ L := by
  rw [mem_levelMap_iff]
  intro g hg
  rw [hψ g, algEquivConjHom_apply_coe, AlgEquiv.symm_apply_apply]
  rw [(mem_levelMap_iff (L := L) (x := x)).mp hx g hg]

/-- **The inverse direction**: the preimage under `e` of a point of `levelMap ψ L` lies in
`levelMap ϕ L`. -/
lemma mem_levelMap_conj_symm (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    {L : IntermediateField K₁ K₁'} {y : Ω} (hy : y ∈ levelMap ψ L) :
    e.symm y ∈ levelMap ϕ L := by
  rw [mem_levelMap_iff]
  intro g hg
  have h1 : ψ g y = y := (mem_levelMap_iff (L := L) (x := y)).mp hy g hg
  have h2 : ψ g y = e (ϕ g (e.symm y)) := by
    rw [hψ g, algEquivConjHom_apply_coe]
  have h3 : e (ϕ g (e.symm y)) = y := by rw [← h2]; exact h1
  have h4 := congrArg (fun z => e.symm z) h3
  simpa using h4

/-- **The level isomorphism induced by `e`**: `e` restricts to an isomorphism from the level
`levelMap ϕ L` of `ϕ` to the level `levelMap ψ L` of its conjugate `ψ`. -/
noncomputable def levelConjEquiv (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (L : IntermediateField K₁ K₁') : ↥(levelMap ϕ L) ≃+* ↥(levelMap ψ L) where
  toFun x := ⟨e (x : K₂'), mem_levelMap_conj ϕ e ψ hψ x.2⟩
  invFun y := ⟨e.symm (y : Ω), mem_levelMap_conj_symm ϕ e ψ hψ y.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp

@[simp] lemma levelConjEquiv_apply_coe
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (L : IntermediateField K₁ K₁') (x : ↥(levelMap ϕ L)) :
    ((levelConjEquiv ϕ e ψ hψ L x : ↥(levelMap ψ L)) : Ω) = e (x : K₂') := rfl

@[simp] lemma levelConjEquiv_symm_apply_coe
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (L : IntermediateField K₁ K₁') (y : ↥(levelMap ψ L)) :
    (((levelConjEquiv ϕ e ψ hψ L).symm y : ↥(levelMap ϕ L)) : K₂') = e.symm (y : Ω) := rfl

/-- **Compatibility of the level isomorphism with the base field**: `e` fixes `K₂`, so the level
isomorphism `levelConjEquiv` is compatible with the two embeddings of `K₂`. -/
lemma mapsBaseLevel_levelConjEquiv
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (L : IntermediateField K₁ K₁') :
    MapsBaseLevel (levelMap ϕ L) (levelMap ψ L) (levelConjEquiv ϕ e ψ hψ L) := by
  constructor
  · intro a
    exact ⟨a, by apply Subtype.ext; simp⟩
  · intro b
    exact ⟨b, by apply Subtype.ext; simp⟩

/-- **The restriction of `ψ g` to the level of `ψ` is the conjugate by `e` of the restriction of
`ϕ g` to the level of `ϕ`.** -/
lemma restrictNormalHom_levelConjEquiv
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L]
    [NumberField ↥(levelMap ϕ L)] [Normal K₂ ↥(levelMap ϕ L)] [Normal K₂ ↥(levelMap ψ L)]
    (g : Gal(K₁'/K₁)) :
    AlgEquiv.restrictNormalHom (levelMap ψ L) (ψ g) =
      conjAlgEquiv (levelConjEquiv ϕ e ψ hψ L) (mapsBaseLevel_levelConjEquiv ϕ e ψ hψ L)
        (AlgEquiv.restrictNormalHom (levelMap ϕ L) (ϕ g)) := by
  ext y
  rw [AlgEquiv.restrictNormalHom_apply, conjAlgEquiv_apply, levelConjEquiv_apply_coe,
    AlgEquiv.restrictNormalHom_apply, levelConjEquiv_symm_apply_coe]
  rw [hψ g, algEquivConjHom_apply_coe]

/-- **The prime of the level of `ψ` below a transported place is the transport of the prime of the
level of `ϕ` below the original place.** -/
lemma primeOfLevel_comap_conj
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (L : IntermediateField K₁ K₁')
    [NumberField ↥(levelMap ϕ L)] [NumberField ↥(levelMap ψ L)]
    (B : ValuationSubring K₂') (hB : B.comap (algebraMap K₂ K₂') ≠ ⊤)
    (B' : ValuationSubring Ω) (hB'e : B' = B.comap (e.symm : Ω →+* K₂'))
    (hB' : B'.comap (algebraMap ↥(levelMap ψ L) Ω) ≠ ⊤) :
    primeOfLevel B' (levelMap ψ L) hB' =
      primeTransport (levelConjEquiv ϕ e ψ hψ L)
        (primeOfLevel B (levelMap ϕ L) (comap_level_ne_top hB (levelMap ϕ L))) := by
  subst hB'e
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥(levelMap ψ L))
  rw [← primeOfLevel_spec (B.comap (e.symm : Ω →+* K₂')) (levelMap ψ L) hB',
    valuationSubringAtPrime_primeTransport (levelConjEquiv ϕ e ψ hψ L)
      (primeOfLevel B (levelMap ϕ L) (comap_level_ne_top hB (levelMap ϕ L))),
    ← primeOfLevel_spec B (levelMap ϕ L) (comap_level_ne_top hB (levelMap ϕ L))]
  ext z
  simp only [ValuationSubring.mem_comap, IntermediateField.algebraMap_apply]
  rfl

end ConjLevel

theorem exists_frobeniusCorrespondence_transport {K₁ K₂ K₁' K₂' Ω : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Field Ω]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [Algebra K₂ Ω] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    [IsSepClosure K₂ Ω] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : LocalCorrespondence ϕ) (b : FrobeniusCorrespondencePlace ϕ hϕ a) (e : K₂' ≃ₐ[K₂] Ω)
    (ψ : Gal(K₁'/K₁) ≃* Gal(Ω/K₂)) (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (hψh : IsHomeomorph ψ) (a' : LocalCorrespondence ψ)
    (ha' : ∀ A : FinitePlaceOf K₁ K₁',
      (a'.placeMap A).1 = (a.placeMap A).1.comap (e.symm : Ω →+* K₂')) :
    FrobeniusCorrespondencePlace ψ hψh a' := by
  intro L hfdL hnormL hnfL hnfL' hnormL' A g hg
  haveI hfd : FiniteDimensional K₂ ↥(levelMap ϕ L) := finiteDimensional_levelMap hϕ L
  haveI hnf : NumberField ↥(levelMap ϕ L) := numberField_levelMap hϕ L
  haveI hnm : Normal K₂ ↥(levelMap ϕ L) := normal_levelMap hϕ L
  have hb : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A).1 (levelMap ϕ L)
        (comap_level_ne_top (a.placeMap A).2 (levelMap ϕ L)))
      (AlgEquiv.restrictNormalHom (levelMap ϕ L) (ϕ g)) := b L A g hg
  rw [primeOfLevel_comap_conj (ϕ := ϕ) (e := e) (ψ := ψ) (hψ := hψ) (L := L)
        (B := (a.placeMap A).1) (hB := (a.placeMap A).2) (B' := (a'.placeMap A).1)
        (hB'e := ha' A) (hB' := comap_level_ne_top (a'.placeMap A).2 (levelMap ψ L)),
    restrictNormalHom_levelConjEquiv (ϕ := ϕ) (e := e) (ψ := ψ) (hψ := hψ) (L := L) (g := g)]
  exact (isFrobAt_primeTransport_iff (mapsBaseLevel_levelConjEquiv ϕ e ψ hψ L)
      (AlgEquiv.restrictNormalHom (levelMap ϕ L) (ϕ g))
      (primeOfLevel (a.placeMap A).1 (levelMap ϕ L)
        (comap_level_ne_top (a.placeMap A).2 (levelMap ϕ L)))).mp hb

end NK.Reconstruct
