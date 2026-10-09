import Mathlib
import Submission.NK.Reconstruct.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place realized by `σ` is the place map of `ϕ`

This file proves `NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap`: if
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` preserves decomposition groups, `σ : K₂' ≃+* K₁'` maps the embedded
`K₂` onto the embedded `K₁` and realizes the place correspondence induced by `ϕ`
(`RealizesPlaceMap`), then the place map `placeMap ϕ h` is exactly the correspondence induced by
`σ`: for every place `A` of `K₁'` over a finite prime of `K₁`,

`(placeMap ϕ h A).comap σ.symm = A`.

The mathematical content is the elementary compatibility of the stabiliser of a place with the
conjugation isomorphism `conjHomEquiv hσ` (`g ↦ σ.symm ∘ g ∘ σ`): the image of the decomposition
group of `A` is the decomposition group of `A.comap σ`
(`NK.Reconstruct.map_conjHomEquiv_decompositionGroup`).  The rest is bookkeeping: `placeMap ϕ h A`
is characterised by its decomposition group (`placeMap_spec`), the two places
`A.comap σ` and `placeMap ϕ h A` lie over finite primes, and places over finite primes are
determined by their decomposition groups (rigidity of places, `decompositionGroup_injective`).
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The image of a decomposition group under conjugation by `σ` is the decomposition group of the
transported place.**  For a ring isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded `K₂` onto the
embedded `K₁`, the stabiliser of a place `A` of `K₁'` in `Gal(K₁'/K₁)` is carried by the conjugation
isomorphism `conjHomEquiv hσ` (`g ↦ σ.symm ∘ g ∘ σ`) onto the stabiliser of the place
`A.comap σ` of `K₂'` in `Gal(K₂'/K₂)`. -/
theorem map_conjHomEquiv_decompositionGroup {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (A : ValuationSubring K₁') :
    (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        ((Submission.NeukirchUchida.conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (A.comap (σ : K₂' →+* K₁')) := by
  have key1 : ∀ (g : Gal(K₁'/K₁)) (z : K₂'),
      (σ : K₂' →+* K₁') (Submission.NeukirchUchida.conj hσ g z) = g (σ z) := by
    intro g z
    rw [Submission.NeukirchUchida.conj_apply]
    simp
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : ∀ y : K₁', y ∈ A ↔ g y ∈ A :=
      (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff A g).mp hg
    refine (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
      (A.comap (σ : K₂' →+* K₁')) (Submission.NeukirchUchida.conj hσ g)).mpr ?_
    intro z
    have h1 := key1 g z
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, h1]
    exact hg' (σ z)
  · intro hx
    have hx' : ∀ z : K₂', z ∈ A.comap (σ : K₂' →+* K₁') ↔
        x z ∈ A.comap (σ : K₂' →+* K₁') :=
      (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
        (A.comap (σ : K₂' →+* K₁')) x).mp hx
    refine ⟨Submission.NeukirchUchida.conj
      (Submission.NeukirchUchida.mapsBase_symm_alg hσ) x, ?_, ?_⟩
    · refine (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff A _).mpr ?_
      intro y
      have h := hx' (σ.symm y)
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at h
      simp at h
      change y ∈ A ↔ σ (x (σ.symm y)) ∈ A
      exact h
    · exact (Submission.NeukirchUchida.conjHomEquiv hσ).right_inv x

/-- **Transporting a place over a finite prime along a base-field-mapping isomorphism.**
If `σ : K₂' ≃+* K₁'` maps the embedded `K₂` onto the embedded `K₁` and `A` is a place of `K₁'` whose
trace on `K₁` is proper, then the place `A.comap σ` of `K₂'` has proper trace on `K₂`. -/
lemma comap_sigma_comap_ne_top {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    {A : ValuationSubring K₁'} (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    (A.comap (σ : K₂' →+* K₁')).comap (algebraMap K₂ K₂') ≠ ⊤ := by
  intro htop
  refine hA (eq_top_iff.mpr ?_)
  intro y _
  rw [ValuationSubring.mem_comap]
  have hy' : algebraMap K₁ K₁' y ∈ (algebraMap K₂ K₂').range.map σ.toRingHom := by
    rw [hσ]
    exact ⟨y, rfl⟩
  rw [Subring.mem_map] at hy'
  obtain ⟨x, hx, hxeq⟩ := hy'
  obtain ⟨x₀, rfl⟩ := RingHom.mem_range.mp hx
  rw [← hxeq]
  have hmem : x₀ ∈ (A.comap (σ : K₂' →+* K₁')).comap (algebraMap K₂ K₂') := by
    rw [htop]
    exact trivial
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at hmem
  exact hmem

/-- **The comap of a place along `σ` followed by the comap along `σ.symm` is the place itself.** -/
lemma comap_symm_comap_eq (σ : K₂' ≃+* K₁') (A : ValuationSubring K₁') :
    (A.comap (σ : K₂' →+* K₁')).comap (σ.symm : K₁' →+* K₂') = A := by
  rw [ValuationSubring.comap_comap, RingEquiv.comp_symm]
  ext x
  rw [ValuationSubring.mem_comap]
  simp

theorem comap_placeMap_eq_of_realizesPlaceMap {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hsub : Submission.NeukirchUchida.RealizesPlaceMap ϕ σ hσ)
    (A : Submission.NeukirchUchida.FinitePlace K₁ K₁') :
    (Submission.NeukirchUchida.placeMap ϕ h A).1.comap (σ.symm : K₁' →+* K₂') = A.1 := by
  have hBC : (Submission.NeukirchUchida.placeMap ϕ h A).1 =
      A.1.comap (σ : K₂' →+* K₁') := by
    refine Submission.NeukirchUchida.decompositionGroup_injective (K₁ := K₂) (K₁' := K₂')
      (Submission.NeukirchUchida.placeMap ϕ h A).2 (comap_sigma_comap_ne_top hσ A.2) ?_
    rw [← Submission.NeukirchUchida.placeMap_spec ϕ h A, ← hsub A.1 A.2,
      map_conjHomEquiv_decompositionGroup hσ A.1]
  rw [hBC]
  exact comap_symm_comap_eq σ A.1

end NK.Reconstruct
