import Mathlib
import Submission.Work.Thom.cupDeltaMaps
import Submission.Work.Thom.cupDeltaInfra
import Submission.Work.Thom.cup_hmvF

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
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

/-! ## Helpers -/

/-- The dual of the component of an epimorphism is a monomorphism. -/
private lemma mono_dualComplexMapComp_of_epi' {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) (n : ℕ) (hf : Epi (f.f n)) :
    Mono (dualComplexMapComp ℤ C D f n) := by
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective ⇑(ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n))
  rw [show ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n)
      = LinearMap.dualMap (ModuleCat.Hom.hom (f.f n)) from rfl]
  exact LinearMap.dualMap_injective_of_surjective ((ModuleCat.epi_iff_surjective _).mp hf)

/-- `relDualIsoComplex` followed by `relIncl` is the dual of the quotient. -/
private lemma relDualIsoComplex_hom_comp_relIncl' (X : TopCat) (A : Set X) :
    (relDualIsoComplex X A).hom ≫ relIncl ℤ X A
      = dualComplexMap ℤ (singularChains ℤ X) (relChains X A) (relChainsProj X A) := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, relDualIsoComplex_hom_f, dualComplexMap_f]
  exact relDualMap_comp_relIncl (X := X) (A := A) k

/-- The comparison `cmpU` of the `U`-piece with the small chains, against the projection. -/
private lemma cmpU_comp_cokerπ (X : TopCat) (A U V : Set X) :
    cmpU X A U V ≫ dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
        (cokernel.π (relMVτ₂U U V A))
      = relIncl ℤ (TopCat.of ↥U) (interAU A U)
        ≫ dualComplexMap ℤ (smallInChains U V U) (singularChains ℤ (TopCat.of ↥U))
            (smallInToSingA U V U) := by
  have h1 : cmpU X A U V
      = (relDualIsoComplex (TopCat.of ↥U) (interAU A U)).inv
        ≫ dualComplexMap ℤ (relMVUU X A U V) (relChains (TopCat.of ↥U) (interAU A U))
            (HMV.etaU A U V) := rfl
  rw [h1, Category.assoc]
  have h2 : dualComplexMap ℤ (relMVUU X A U V) (relChains (TopCat.of ↥U) (interAU A U))
        (HMV.etaU A U V)
      ≫ dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V) (cokernel.π (relMVτ₂U U V A))
      = dualComplexMap ℤ (smallInChains U V U) (relChains (TopCat.of ↥U) (interAU A U))
          (smallInToSingA U V U ≫ relChainsProj (TopCat.of ↥U) (interAU A U)) := by
    rw [← dualComplexMap_comp, HMV.etaU_comp]
  rw [h2, dualComplexMap_comp]
  rw [← Category.assoc, ← relDualIsoComplex_hom_comp_relIncl']
  rw [Iso.inv_hom_id_assoc]

/-- The chain map `smallInToSingA U V U` composed with the inclusion `U ↪ X` is the inclusion of
the small-in-`U` chains. -/
private lemma smallInToSingA_comp_chainMap (X : TopCat) (U V : Set X) :
    smallInToSingA U V U ≫ chainMap ℤ (TopCat.of ↥U) X (subtypeIncl X U)
      = SSet.chainComplexMap (smallInSubcomplex U V U).ι (ModuleCat.of ℤ ℤ) := by
  show SSet.chainComplexMap (smallInLift U V U) (ModuleCat.of ℤ ℤ)
      ≫ SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X U)) (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (smallInSubcomplex U V U).ι (ModuleCat.of ℤ ℤ)
  have hcomp : SSet.chainComplexMap (smallInLift U V U ≫ TopCat.toSSet.map (subtypeIncl X U))
        (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (smallInLift U V U) (ModuleCat.of ℤ ℤ)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X U)) (ModuleCat.of ℤ ℤ) :=
    Functor.map_comp (self := (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (f := smallInLift U V U) (g := TopCat.toSSet.map (subtypeIncl X U))
  rw [← hcomp, smallInLift_comp]

/-- The restriction `restrIn` of the global cochain `t` to the small-in-`U` chains is the pullback
of `t` to `U` followed by the inclusion of the small chains. -/
private lemma restrIn_eq_relRestrCochain (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((relComplex ℤ X A).X n)) :
    restrIn X U V U n t.1
      = ((relRestrCochain A U n t).1).comp ((smallInToSingA U V U).f n).hom := by
  rw [show restrIn X U V U n t.1
      = t.1.comp ((SSet.chainComplexMap (smallInSubcomplex U V U).ι
          (ModuleCat.of ℤ ℤ)).f n).hom from LinearMap.dualMap_apply' _ _]
  rw [relRestrCochain_coe A U n t, LinearMap.comp_assoc]
  congr 1
  rw [show ((chainMap ℤ (TopCat.of ↥U) X (subtypeIncl X U)).f n).hom
        ∘ₗ ((smallInToSingA U V U).f n).hom
      = ((SSet.chainComplexMap (smallInSubcomplex U V U).ι (ModuleCat.of ℤ ℤ)).f n).hom
      from congrArg (fun φ => ModuleCat.Hom.hom (φ.f n))
        (smallInToSingA_comp_chainMap X U V)]

/-- Naturality of the cup with the inclusion of the small chains of the `U`-piece. -/
private lemma cupCompat_chain (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : ↥((relComplex ℤ X A).X n))
    (ht : cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    (relIncl ℤ (TopCat.of ↥U) (interAU ∅ U)).f p
      ≫ (dualComplexMap ℤ (smallInChains U V U) (singularChains ℤ (TopCat.of ↥U))
          (smallInToSingA U V U)).f p
      ≫ cupInCochain X U V U n p t.1
    = (cupRightComplex (relRestrCochain A U n t) (interAU ∅ U)
          (cupComm_U X A U V n t ht)).f p
      ≫ (relIncl ℤ (TopCat.of ↥U) (interAU A U)).f (p + n)
      ≫ (dualComplexMap ℤ (smallInChains U V U) (singularChains ℤ (TopCat.of ↥U))
          (smallInToSingA U V U)).f (p + n) := by
  have hrestr := restrIn_eq_relRestrCochain X A U V n t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro w
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [dualComplexMap_apply_hom]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [dualComplexMap_apply_hom]
  simp only [cupInCochain, ModuleCat.hom_ofHom, LinearMap.comp_apply, relIncl_f,
    cupRightComplex, cupRightLM]
  change cup ℤ (smallInSSet U V U) (c.1.comp ((smallInToSingA U V U).f p).hom)
        (restrIn X U V U n t.1) w
      = cup ℤ (TopCat.toSSet.obj (TopCat.of ↥U)) c.1 ((relRestrCochain A U n t).1)
          ((ModuleCat.Hom.hom ((smallInToSingA U V U).f (p + n))) w)
  rw [hrestr]
  exact congrArg (fun m => ModuleCat.Hom.hom m w)
    (cupHom_chainComplexMap (S := smallInSSet U V U) (T := TopCat.toSSet.obj (TopCat.of ↥U))
      (g := smallInLift U V U) (n := p) (m := n)
      (α := c.1) (β := (relRestrCochain A U n t).1)).symm

/-- **The honest cup and the descended cup agree through the comparison maps.** -/
private lemma cupRightComplex_cupU_comm (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : ↥((relComplex ℤ X A).X n))
    (ht : cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    (Work.Cohomology.cmpU X ∅ U V).f p ≫ cupU X A U V n p t.1 t.2
      = (cupRightComplex (relRestrCochain A U n t) (interAU ∅ U)
            (cupComm_U X A U V n t ht)).f p
        ≫ (Work.Cohomology.cmpU X A U V).f (p + n) := by
  have hm : Mono ((dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
      (cokernel.π (relMVτ₂U U V A))).f (p + n)) :=
    mono_dualComplexMapComp_of_epi' _ _ inferInstance
  refine (cancel_mono ((dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
      (cokernel.π (relMVτ₂U U V A))).f (p + n))).mp ?_
  have hA : cupU X A U V n p t.1 t.2
        ≫ (dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
            (cokernel.π (relMVτ₂U U V A))).f (p + n)
      = (dualComplexMap ℤ (smallInChains U V U) (relMVUU X ∅ U V)
            (cokernel.π (relMVτ₂U U V ∅))).f p ≫ cupInCochain X U V U n p t.1 := by
    unfold cupU
    rw [Category.assoc, cupDescendRel_compU (t := t.1) (ht := t.2)]
  rw [Category.assoc, hA]
  have hB : (Work.Cohomology.cmpU X ∅ U V).f p
        ≫ (dualComplexMap ℤ (smallInChains U V U) (relMVUU X ∅ U V)
            (cokernel.π (relMVτ₂U U V ∅))).f p
      = (relIncl ℤ (TopCat.of ↥U) (interAU ∅ U)).f p
        ≫ (dualComplexMap ℤ (smallInChains U V U) (singularChains ℤ (TopCat.of ↥U))
            (smallInToSingA U V U)).f p := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun φ => φ.f p) (cmpU_comp_cokerπ X ∅ U V)
  rw [← Category.assoc, hB]
  have hC : (Work.Cohomology.cmpU X A U V).f (p + n)
        ≫ (dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
            (cokernel.π (relMVτ₂U U V A))).f (p + n)
      = (relIncl ℤ (TopCat.of ↥U) (interAU A U)).f (p + n)
        ≫ (dualComplexMap ℤ (smallInChains U V U) (singularChains ℤ (TopCat.of ↥U))
            (smallInToSingA U V U)).f (p + n) := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun φ => φ.f (p + n)) (cmpU_comp_cokerπ X A U V)
  conv_rhs => rw [Category.assoc]
  rw [hC]
  conv_lhs => rw [Category.assoc]
  exact cupCompat_chain X A U V n p t ht

/-- `sigmaU` and the descended cup `cupU` agree. -/
private lemma sigmaU_eq_cupU (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : ↥((relComplex ℤ X A).X n))
    (ht : cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    (sigmaU X A U V n t (cupComm_U X A U V n t ht)).f p
      = cupU X A U V n p t.1 t.2 := by
  haveI hc : IsIso (Work.Cohomology.cmpU X ∅ U V) := isIso_cmpU X ∅ U V
  have hunf : (sigmaU X A U V n t (cupComm_U X A U V n t ht)).f p
      = (CategoryTheory.inv (Work.Cohomology.cmpU X ∅ U V)).f p
        ≫ (cupRightComplex (relRestrCochain A U n t) (interAU ∅ U)
            (cupComm_U X A U V n t ht)).f p
        ≫ (Work.Cohomology.cmpU X A U V).f (p + n) := by
    unfold sigmaU
    rw [CategoryTheory.asIso_inv, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Tsq.shMap_f]
  rw [hunf, ← cupRightComplex_cupU_comm X A U V n p t ht]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f,
    Category.id_comp]

end

end Work.Thom

namespace Work.Thom

open Work.Cohomology

noncomputable section

theorem alphaU_tau1 (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relMVUU X ∅ U V)
          (Work.Cohomology.relMVTopC X ∅ U V) (Work.Cohomology.HMV.alphaU X ∅ U V))
        (Work.Thom.sigmaU X A U V n t (Work.Thom.cupComm_U X A U V n t ht))
      = CategoryTheory.CategoryStruct.comp (Work.Thom.tau1 X A U V n t ht)
          (Work.Thom.Tsq.shMap (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relMVUU X A U V)
            (Work.Cohomology.relMVTopC X A U V) (Work.Cohomology.HMV.alphaU X A U V)) n) := by
  apply HomologicalComplex.hom_ext
  intro p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Tsq.shMap_f]
  rw [show (tau1 X A U V n t ht).f p = cupTop X A U V n p t.1 t.2 from rfl]
  rw [cupTop_alphaU]
  rw [sigmaU_eq_cupU X A U V n p t ht]

end

end Work.Thom

