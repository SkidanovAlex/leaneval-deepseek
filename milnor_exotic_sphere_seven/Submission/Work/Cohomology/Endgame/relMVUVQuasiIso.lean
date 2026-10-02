import Submission.Work.Cohomology.Endgame.overlapQuasiIso
import Submission.Work.Cohomology.relMV_shortExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative small chains of the overlap compute the relative chains of `U ∩ V`

The overlap term of the relative Mayer–Vietoris sequence is
`relMVUV X A U V = C^{U,V}(U ∩ V, U ∩ V ∩ A)`, the small chains lying in `U ∩ V` modulo those
lying in `U ∩ V ∩ A`.  For an open cover `U ∪ V = X` the comparison with the genuine relative
singular chains of the subspace `U ∩ V` (with `A` traced back by the inclusion) is a
quasi-isomorphism:

`relMVUV_quasiIso : ∀ n, IsIso (homologyMap (relMVUVPhi X A U V) n)`.

This is the second of the three quasi-isomorphisms needed by the transgression identity
(`Endgame/NOTES.md` §20); the top term is `relMV_quasiIso` and the absolute term of the overlap is
`isIso_smallInToSingA`.

The only non-formal ingredient is the compatibility of the two liftings of the overlap
(`smallInLift_inter_natural`): the small-in-`A` simplices of `U ∩ V` lift to the subspace
`U ∩ V ∩ A`, which is canonically the same as the part of the subspace `U ∩ V` lying in `A`
(`interSubHomeo`).
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- `inclChains` in terms of `SSet.chainComplexMap` (definitional). -/
theorem inclChains_eq_map (X : TopCat) (A : Set X) :
    inclChains X A
      = SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of ℤ ℤ) := rfl

/-- The inclusion `U ∩ V ∩ A ⊆ U ∩ V`, as a morphism of the corresponding subcomplexes of small
simplices. -/
def subInclSSet (A U V : Set X) :
    smallInSSet U V (U ∩ V ∩ A) ⟶ smallInSSet U V (U ∩ V) :=
  Subfunctor.homOfLe (by
    intro n x hx
    exact ⟨hx.1, hx.2.trans (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)⟩)

/-- The composite of `subInclSSet` with the inclusion of the small simplices is the inclusion of the
small simplices lying in `U ∩ V ∩ A`. -/
theorem subInclSSet_comp (A U V : Set X) :
    subInclSSet A U V ≫ (smallInSubcomplex U V (U ∩ V)).ι
      = (smallInSubcomplex U V (U ∩ V ∩ A)).ι :=
  Subfunctor.homOfLe_ι _

/-- The canonical identification of the two descriptions of `U ∩ V ∩ A`. -/
theorem subtypeIncl_interSubHomeo (A U V : Set X) :
    (interSubHomeo X A U V).hom
        ≫ subtypeIncl (TopCat.of ↥(U ∩ V)) ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)
        ≫ subtypeIncl X (U ∩ V)
      = subtypeIncl X (U ∩ V ∩ A) := by
  apply TopCat.hom_ext
  ext p
  rfl

/-- **The naturality of the overlap lift**: lifting a small-in-`A` simplex of the overlap to `A` or
lifting it first to `U ∩ V` and then taking its part in `A` give the same simplex. -/
theorem smallInLift_inter_natural (A U V : Set X) :
    subInclSSet A U V ≫ smallInLift U V (U ∩ V)
      = smallInLift U V (U ∩ V ∩ A)
        ≫ TopCat.toSSet.map (interSubHomeo X A U V).hom
        ≫ TopCat.toSSet.map (subtypeIncl (TopCat.of ↥(U ∩ V))
            ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)) := by
  apply (cancel_mono (TopCat.toSSet.map (subtypeIncl X (U ∩ V)))).1
  have hL : (subInclSSet A U V ≫ smallInLift U V (U ∩ V))
      ≫ TopCat.toSSet.map (subtypeIncl X (U ∩ V))
      = (smallInSubcomplex U V (U ∩ V ∩ A)).ι := by
    rw [Category.assoc, smallInLift_comp, subInclSSet_comp]
  have hR : (smallInLift U V (U ∩ V ∩ A)
        ≫ TopCat.toSSet.map (interSubHomeo X A U V).hom
        ≫ TopCat.toSSet.map (subtypeIncl (TopCat.of ↥(U ∩ V))
            ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)))
      ≫ TopCat.toSSet.map (subtypeIncl X (U ∩ V))
      = (smallInSubcomplex U V (U ∩ V ∩ A)).ι := by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      subtypeIncl_interSubHomeo, smallInLift_comp]
  exact hL.trans hR.symm

/-- The chain level form of `smallInLift_inter_natural`. -/
theorem subInclChain_natural (A U V : Set X) :
    subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
      ≫ SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
    = SSet.chainComplexMap (smallInLift U V (U ∩ V ∩ A)) (ModuleCat.of ℤ ℤ)
      ≫ SSet.chainComplexMap (TopCat.toSSet.map (interSubHomeo X A U V).hom) (ModuleCat.of ℤ ℤ)
      ≫ inclChains (TopCat.of ↥(U ∩ V)) ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A) := by
  have h := congrArg (fun (f : smallInSSet U V (U ∩ V ∩ A) ⟶
      TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) => SSet.chainComplexMap f (ModuleCat.of ℤ ℤ))
    (smallInLift_inter_natural A U V)
  simpa only [inclChains_eq_map, subInclChain, subInclSSet, Functor.map_comp, Category.assoc]
    using h

/-- The comparison map from the relative small chains of the overlap to the relative singular
chains of the subspace `U ∩ V`. -/
noncomputable def relMVUVPhi (X : TopCat) (A U V : Set X) :
    relMVUV X A U V ⟶ relChains (TopCat.of ↥(U ∩ V))
      ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A) :=
  cokernel.desc (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))
    (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
      ≫ cokernel.π (inclChains (TopCat.of ↥(U ∩ V)) ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)))
    (by
      calc subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
            ≫ (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
              ≫ cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
                  ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)))
          = (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
              ≫ SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ))
            ≫ cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
                ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)) :=
              (Category.assoc _ _ _).symm
        _ = 0 := by
              rw [subInclChain_natural]
              simp only [Category.assoc, cokernel.condition, comp_zero])

/-- The computation rule for `relMVUVPhi`. -/
theorem relMVUVPhi_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)) ≫ relMVUVPhi X A U V
      = SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
        ≫ cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
            ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)) :=
  cokernel.π_desc _ _ _

/-- The chain map underlying `relMVUVPhi` on the first term. -/
noncomputable abbrev relMVUVPhiTop (X : TopCat) (A U V : Set X) :
    smallInChains U V (U ∩ V ∩ A)
      ⟶ singularChains ℤ (TopCat.of ↥((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)) :=
  SSet.chainComplexMap (smallInLift U V (U ∩ V ∩ A)) (ModuleCat.of ℤ ℤ)
    ≫ SSet.chainComplexMap (TopCat.toSSet.map (interSubHomeo X A U V).hom) (ModuleCat.of ℤ ℤ)

/-- **The relative small chains of the overlap compute the relative singular chains of the
subspace `U ∩ V`.** -/
theorem relMVUV_quasiIso (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relMVUVPhi X A U V) n) := by
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))
      (cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)))
      (cokernel.condition (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)))
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)))
      (mono_subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)) inferInstance
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    hPairShort (TopCat.of ↥(U ∩ V)) ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)
  have hS₂ : S₂.ShortExact := hPairShort_shortExact _ _
  let ψ : S₁ ⟶ S₂ :=
    { τ₁ := relMVUVPhiTop X A U V
      τ₂ := SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
      τ₃ := relMVUVPhi X A U V
      comm₁₂ := by
        show relMVUVPhiTop X A U V
            ≫ inclChains (TopCat.of ↥(U ∩ V)) ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)
          = subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
            ≫ SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
        exact (subInclChain_natural A U V).symm
      comm₂₃ := by
        show SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
            ≫ cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
                ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A))
          = cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)) ≫ relMVUVPhi X A U V
        exact (relMVUVPhi_comp X A U V).symm }
  have hq1 : QuasiIso ψ.τ₁ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    show IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (smallInLift U V (U ∩ V ∩ A)) (ModuleCat.of ℤ ℤ)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (interSubHomeo X A U V).hom)
            (ModuleCat.of ℤ ℤ)) i)
    rw [HomologicalComplex.homologyMap_comp]
    haveI : IsIso (SSet.chainComplexMap (TopCat.toSSet.map (interSubHomeo X A U V).hom)
        (ModuleCat.of ℤ ℤ)) :=
      Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
        (TopCat.toSSet.map (interSubHomeo X A U V).hom)
    haveI h1 : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (smallInLift U V (U ∩ V ∩ A)) (ModuleCat.of ℤ ℤ)) i) :=
      isIso_smallInToSingA U V (U ∩ V ∩ A) hU hV hcov i
    infer_instance
  have hq2 : QuasiIso ψ.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    show IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)) i)
    exact isIso_smallInToSingA U V (U ∩ V) hU hV hcov i
  have hq3 : QuasiIso ψ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hS₁ hS₂ hq1 hq2
  have h := hq3.quasiIsoAt n
  rw [quasiIsoAt_iff_isIso_homologyMap] at h
  exact h

end

end Work.Cohomology
