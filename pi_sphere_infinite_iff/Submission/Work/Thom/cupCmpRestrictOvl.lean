import Mathlib
import Submission.Work.Thom.cupDeltaInfra
import Submission.Work.Thom.transgressionFleetDefs
import Submission.Work.Thom.cup_hmvG
import Submission.Work.Thom.relRestrCochain_dcocycle
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.hmv_naturality
import Submission.Work.Cohomology.cupNatural

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

namespace Work.Thom

open Work.Cohomology

noncomputable section

set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Work.Cohomology.relComplex
attribute [local implicit_reducible] Work.Cohomology.singularCochainComplex
attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor
attribute [local implicit_reducible] ComplexShape.Embedding.mk'
attribute [local implicit_reducible] HomologicalComplex.restriction
attribute [local implicit_reducible] TopCat.toSSet
attribute [local implicit_reducible] Work.Cohomology.relKern
attribute [local implicit_reducible] Work.Cohomology.smallInSubcomplex
attribute [local implicit_reducible] Work.Cohomology.smallSubcomplex
attribute [local implicit_reducible] Work.Cohomology.dualComplex
attribute [local implicit_reducible] CochainComplex.of
attribute [local implicit_reducible] Work.Cohomology.dualObj

/-- The inverse duality isomorphism followed by the quotient projection is the inclusion. -/
lemma relDualIsoComplex_inv_comp_relChainsProj (X : TopCat) (A : Set X) :
    (relDualIsoComplex X A).inv
        ≫ dualComplexMap ℤ (singularChains ℤ X) (relChains X A) (relChainsProj X A)
      = relIncl ℤ X A := by
  rw [relChainsProj, ← hmvRelDualIsoComplex_hom_comp_relIncl X A]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The comparison `cmpW` of the overlap against the projection to the small chains.** -/
lemma cmpW_comp_cokerπ (X : TopCat) (A U V : Set X) :
    cmpW X A U V
        ≫ dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X A U V)
            (cokernel.π (relMVτ₁ U V A))
      = relIncl ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
        ≫ dualComplexMap ℤ (smallInChains U V (U ∩ V))
            (singularChains ℤ (TopCat.of ↥(U ∩ V)))
            (smallInToSingA U V (U ∩ V)) := by
  have h1 : cmpW X A U V
      = (relDualIsoComplex (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))).inv
        ≫ dualComplexMap ℤ (relMVUV X A U V)
            (relChains (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)))
            (relMVUVPhi X A U V) := rfl
  rw [h1, Category.assoc]
  have h2 : dualComplexMap ℤ (relMVUV X A U V)
        (relChains (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))) (relMVUVPhi X A U V)
      ≫ dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X A U V)
          (cokernel.π (relMVτ₁ U V A))
      = dualComplexMap ℤ (smallInChains U V (U ∩ V))
          (relChains (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)))
          (smallInToSingA U V (U ∩ V) ≫ relChainsProj (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))) := by
    rw [← dualComplexMap_comp, hmv_relMVUVPhi_comp]
  rw [h2, dualComplexMap_comp]
  rw [← Category.assoc, relDualIsoComplex_inv_comp_relChainsProj]

/-- The chain map `smallInToSingA U V (U∩V)` composed with the inclusion is the inclusion of the
small-in-`(U∩V)` chains. -/
lemma smallInToSingA_comp_chainMap_W (X : TopCat) (U V : Set X) :
    smallInToSingA U V (U ∩ V) ≫ chainMap ℤ (TopCat.of ↥(U ∩ V)) X (subtypeIncl X (U ∩ V))
      = SSet.chainComplexMap (smallInSubcomplex U V (U ∩ V)).ι (ModuleCat.of ℤ ℤ) := by
  show SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
      ≫ SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X (U ∩ V))) (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (smallInSubcomplex U V (U ∩ V)).ι (ModuleCat.of ℤ ℤ)
  have hcomp : SSet.chainComplexMap (smallInLift U V (U ∩ V) ≫ TopCat.toSSet.map (subtypeIncl X (U ∩ V)))
        (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X (U ∩ V))) (ModuleCat.of ℤ ℤ) :=
    Functor.map_comp (self := (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (f := smallInLift U V (U ∩ V)) (g := TopCat.toSSet.map (subtypeIncl X (U ∩ V)))
  rw [← hcomp, smallInLift_comp]

/-- The restriction `restrIn` to the small-in-`(U∩V)` chains is the pullback of the restriction of
`t` to `U ∩ V`. -/
lemma restrIn_eq_relRestrCochain_W (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((relComplex ℤ X A).X n)) :
    restrIn X U V (U ∩ V) n t.1
      = ((relRestrCochain A (U ∩ V) n t).1).comp ((smallInToSingA U V (U ∩ V)).f n).hom := by
  rw [show restrIn X U V (U ∩ V) n t.1
      = t.1.comp ((SSet.chainComplexMap (smallInSubcomplex U V (U ∩ V)).ι
          (ModuleCat.of ℤ ℤ)).f n).hom from LinearMap.dualMap_apply' _ _]
  rw [relRestrCochain_coe A (U ∩ V) n t, LinearMap.comp_assoc]
  congr 1
  rw [show ((chainMap ℤ (TopCat.of ↥(U ∩ V)) X (subtypeIncl X (U ∩ V))).f n).hom
        ∘ₗ ((smallInToSingA U V (U ∩ V)).f n).hom
      = ((SSet.chainComplexMap (smallInSubcomplex U V (U ∩ V)).ι (ModuleCat.of ℤ ℤ)).f n).hom
      from congrArg (fun φ => ModuleCat.Hom.hom (φ.f n))
        (smallInToSingA_comp_chainMap_W X U V)]

/-- **The cup with the restriction of a relative cocycle commutes with the comparison `cmpW`.** -/
theorem cupCmpRestrictOvl (X : TopCat) (A U V : Set X) (n k : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (c : ↥((Work.Cohomology.relComplex ℤ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU ∅ (U ∩ V))).X k)) :
    (Work.Cohomology.cmpW X A U V).f (k + n)
        ((Work.Thom.cupRightLM (Work.Thom.relRestrCochain A (U ∩ V) n t)
          (Work.Cohomology.interAU ∅ (U ∩ V)) k) c)
      = Work.Thom.cupUV X A U V n k t.1 t.2 ((Work.Cohomology.cmpW X ∅ U V).f k c) := by
  have hmono : Mono (dualComplexMapComp ℤ (smallInChains U V (U ∩ V)) (relMVUV X A U V)
      (cokernel.π (relMVτ₁ U V A)) (k + n)) :=
    mono_dualComplexMapComp_of_epi _ _ (epi_cokernelπ_f _ _)
  have hm : Mono ((dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X A U V)
      (cokernel.π (relMVτ₁ U V A))).f (k + n)) := hmono
  apply (ModuleCat.mono_iff_injective _).1 hm
  have hA : cupUV X A U V n k t.1 t.2
        ≫ (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X A U V)
            (cokernel.π (relMVτ₁ U V A))).f (k + n)
      = (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X ∅ U V)
            (cokernel.π (relMVτ₁ U V ∅))).f k
        ≫ cupHomMap X U V (U ∩ V) n k t.1 := by
    rw [cupUV, Category.assoc]
    erw [cupHomMap_spec]
  have hB : (cmpW X ∅ U V).f k
        ≫ (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X ∅ U V)
            (cokernel.π (relMVτ₁ U V ∅))).f k
      = (relIncl ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V))).f k
        ≫ (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (singularChains ℤ (TopCat.of ↥(U ∩ V)))
            (smallInToSingA U V (U ∩ V))).f k := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun φ => φ.f k) (cmpW_comp_cokerπ X ∅ U V)
  have hC : (cmpW X A U V).f (k + n)
        ≫ (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X A U V)
            (cokernel.π (relMVτ₁ U V A))).f (k + n)
      = (relIncl ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))).f (k + n)
        ≫ (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (singularChains ℤ (TopCat.of ↥(U ∩ V)))
            (smallInToSingA U V (U ∩ V))).f (k + n) := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun φ => φ.f (k + n)) (cmpW_comp_cokerπ X A U V)
  have hAz := congrArg (fun (m : (dualComplex ℤ (relMVUV X ∅ U V)).X k
        ⟶ (dualComplex ℤ (smallInChains U V (U ∩ V))).X (k + n)) =>
      ModuleCat.Hom.hom m ((cmpW X ∅ U V).f k c)) hA
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hAz
  have hBz := congrArg (fun (m : (relComplex ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V))).X k
        ⟶ (dualComplex ℤ (smallInChains U V (U ∩ V))).X k) =>
      ModuleCat.Hom.hom m c) hB
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hBz
  have hCz := congrArg (fun (m : (relComplex ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))).X (k + n)
        ⟶ (dualComplex ℤ (smallInChains U V (U ∩ V))).X (k + n)) =>
      ModuleCat.Hom.hom m
        ((cupRightLM (relRestrCochain A (U ∩ V) n t) (interAU ∅ (U ∩ V)) k) c)) hC
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hCz
  rw [hCz, hAz, hBz]
  erw [cupHomMap_apply]
  simp only [relIncl_f, ModuleCat.hom_ofHom]
  show ((SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f (k + n)).hom.dualMap
        (cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) c.1 (relRestrCochain A (U ∩ V) n t).1)
      = cup ℤ (smallInSSet U V (U ∩ V))
          (((SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f k).hom.dualMap c.1)
          (restrIn X U V (U ∩ V) n t.1)
  rw [← cupNatural ℤ (smallInLift U V (U ∩ V)) c.1 (relRestrCochain A (U ∩ V) n t).1]
  rw [restrIn_eq_relRestrCochain_W X A U V n t]
  rfl

end

end Work.Thom

