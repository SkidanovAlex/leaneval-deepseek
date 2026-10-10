import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.ReconstructField.Weak
import Submission.NK.ReconstructField.ncard_primesOver_levelMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

open scoped Pointwise

/-- The image of a valuation subring under an algebra automorphism is the preimage under the
inverse automorphism: `σ • A = A.comap σ.symm`.  (The `AlgEquiv` form of
`Commons.RingTheory.Valuation.ValuationSubring.smul_eq_comap_symm`.) -/
private lemma smul_eq_comap_symm_algEquiv {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (σ : K' ≃ₐ[K] K') (A : ValuationSubring K') :
    σ • A = A.comap (σ.symm : K' →+* K') := by
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_comap]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [← hxs]
    change σ.symm (σ s) ∈ A
    rw [AlgEquiv.symm_apply_apply]
    exact hs
  · intro hh
    exact ⟨σ.symm x, hh, σ.apply_symm_apply x⟩

/-- An element of `Gal(K'/K)` fixing an intermediate field `L` pointwise does not move the trace of
a place of `K'` on `L`. -/
private lemma smul_comap_eq_of_mem_fixingSubgroup {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (L : IntermediateField K K') (g : Gal(K'/K)) (hg : g ∈ L.fixingSubgroup)
    (A : ValuationSubring K') :
    (g • A).comap (algebraMap ↥L K') = A.comap (algebraMap ↥L K') := by
  have hmem : ∀ y ∈ (L : Set K'), g⁻¹ y = y := by
    have h1 : g⁻¹ ∈ L.fixingSubgroup := L.fixingSubgroup.inv_mem hg
    intro y hy
    exact (IntermediateField.mem_fixingSubgroup_iff L g⁻¹).mp h1 y hy
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_comap]
  change g⁻¹ (algebraMap ↥L K' x) ∈ A ↔ algebraMap ↥L K' x ∈ A
  rw [hmem (algebraMap ↥L K' x) x.2]

/-- **Injectivity of the level-prime of the place correspondence.**  If the places `a.placeMap A`
and `a.placeMap A'` of `K₂'` corresponding to the two places `A`, `A'` of `K₁'` restrict to the
same prime of the ring of integers of the image level `levelMap ϕ L`, then `A` and `A'` restrict to
the same place of `L`.

The proof is the transitivity of the Galois action on the extensions of a place: by
`Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq` there is `σ ∈ Gal(K₂'/K₂)`
fixing `levelMap ϕ L` pointwise with `σ • (a.placeMap A).1 = (a.placeMap A').1`; under the Galois
correspondence of levels (`NK.Reconstruct.fixingSubgroup_levelMap`) this `σ` is `ϕ g` for some
`g ∈ Gal(K₁'/L)`; Galois-equivariance of `a.placeMap` (`a.map_smul`) then forces `g • A = A'`,
whence `A` and `A'` have the same trace on `L`. -/
theorem comap_eq_of_primeOfLevel_placeMap_eq
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (A A' : NK.Reconstruct.FinitePlaceOf K₁ K₁')
    (h : NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) =
      NK.Reconstruct.primeOfLevel (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L))) :
    A.1.comap (algebraMap ↥L K₁') = A'.1.comap (algebraMap ↥L K₁') := by
  -- The hypothesis says that the two places of `K₂'` have the same trace on the image level.
  have hBT : (a.placeMap A).1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') =
      (a.placeMap A').1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') := by
    rw [NK.Reconstruct.primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)),
        NK.Reconstruct.primeOfLevel_spec (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L)
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L)),
        h]
  -- Transitivity of the Galois action at the image level.
  obtain ⟨σ, hσfix, hσB⟩ := Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq
    (K := K₂) (K' := K₂') (NK.Reconstruct.levelMap ϕ L) (a.placeMap A).1 (a.placeMap A').1
    (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) hBT
  -- `σ` is the image under `ϕ` of an element fixing `L` pointwise.
  obtain ⟨g, hgL, hgσ⟩ : ∃ g ∈ L.fixingSubgroup, ϕ g = σ := by
    have hfix : σ ∈ (NK.Reconstruct.levelMap ϕ L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hσfix ⟨x, hx⟩
    rw [NK.Reconstruct.fixingSubgroup_levelMap hϕ L] at hfix
    exact Subgroup.mem_map.mp hfix
  -- Galois-equivariance of the place map turns this into `g • A = A'`.
  have hplace : NK.Reconstruct.placeSmul₂ (ϕ g) (a.placeMap A) = a.placeMap A' := by
    have h1 : σ • (a.placeMap A).1 = (a.placeMap A').1 := by
      rw [smul_eq_comap_symm_algEquiv σ (a.placeMap A).1, hσB]
    refine Subtype.ext ?_
    rw [NK.Reconstruct.placeSmul₂_val, hgσ]
    exact h1
  have hAeq : NK.Reconstruct.placeSmul g A = A' := by
    apply a.placeMap.injective
    rw [a.map_smul g A, hplace]
  -- An element fixing `L` pointwise does not move the trace on `L`.
  have hval : g • A.1 = A'.1 := congrArg Subtype.val hAeq
  rw [← hval]
  exact (smul_comap_eq_of_mem_fixingSubgroup L g hgL A.1).symm

end NK.ReconstructField
