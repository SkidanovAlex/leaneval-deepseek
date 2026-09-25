import Mathlib
import Submission.Commons.Algebra.Homology.homologyUnop_hom_naturality
import Submission.NK.RepresentationTheory.GroupCohomology.res_counit_defs

/-
# The chain-level comparison of `psiMap` with the restriction–coind comparison

`coindIso_hom_eq` expands Shapiro's isomorphism
`coindIso : Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` (Mathlib,
`RepresentationTheory/Homological/GroupCohomology/Shapiro.lean`) along the chain-level data
supplied by `res_counit_defs.lean`: the inhomogeneous-cochains comparison `ι`, the
restriction–coind comparison `λ = lambdaIso`, and the chain map `ψ = psiMap` induced by the
canonical map `barComplex k S ⟶ Res(barComplex k G)`.

The mathematical content is the identification of the two canonical ways of comparing the
`Ext`-computations for two projective resolutions of the same object: the `isoExt`-comparison
is the homology map of the induced morphism on `linearYonedaObj`, which at the level of the
two inhomogeneous-cochain complexes is nothing but `ψ`.  The general statement of that
comparison is `isoExt_inv_comp_hom` below (a self-contained transcription of the corresponding
`ℤ`-linear lemma used by
`Commons/RepresentationTheory/GroupCohomology/unit_coindIso_eq_resNatTrans.lean`).
-/

namespace NK.RepresentationTheory.GroupCohomology

open CategoryTheory Limits


variable {R : Type*} [Ring R] {C : Type*} [Category* C] [Abelian C] [Linear R C] [EnoughProjectives C]

set_option backward.isDefEq.respectTransparency false in
private lemma isoLeftDerivedObj_comp {D : Type*} [Category* D] [Abelian D] {X : C}
    (P Q : ProjectiveResolution X) (q : P.complex ⟶ Q.complex) (hq : q ≫ Q.π = P.π)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom =
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map q) := by
  have hcomm : q.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ (𝟙 X) := by
    have h := congrArg (fun (m : P.complex ⟶ (ChainComplex.single₀ C).obj X) => m.f 0) hq
    rw [HomologicalComplex.comp_f] at h
    erw [h, Category.comp_id]
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 X) P Q q hcomm F n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [show (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map q =
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map q) from rfl] at h
  rw [h]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma isoExt_inv_comp_hom {X : C} (P Q : ProjectiveResolution X)
    (q : P.complex ⟶ Q.complex) (hq : q ≫ Q.π = P.π) (Y : C) (n : ℕ) :
    (Q.isoExt n Y).inv ≫ (P.isoExt n Y).hom =
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map
        ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
          (((Functor.mapHomologicalComplex ((linearYoneda R C).obj Y).rightOp
            (ComplexShape.down ℕ)).map q)).op) := by
  simp only [ProjectiveResolution.isoExt]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.unop_hom, Iso.unop_inv]
  have hcomp : (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
      (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop
      = ((HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) n).map
          ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).map q)).unop := by
    rw [← CategoryTheory.unop_comp (f := (P.isoLeftDerivedObj
        ((linearYoneda R C).obj Y).rightOp n).inv) (g := (Q.isoLeftDerivedObj
        ((linearYoneda R C).obj Y).rightOp n).hom)]
    rw [isoLeftDerivedObj_comp (D := (ModuleCat R)ᵒᵖ) P Q q hq ((linearYoneda R C).obj Y).rightOp n]
  have h1 : (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
      (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop
      = ((HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) n).map
          ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).map q)).unop := by
    rw [← CategoryTheory.unop_comp (f := (P.isoLeftDerivedObj
        ((linearYoneda R C).obj Y).rightOp n).inv) (g := (Q.isoLeftDerivedObj
        ((linearYoneda R C).obj Y).rightOp n).hom)]
    rw [isoLeftDerivedObj_comp (D := (ModuleCat R)ᵒᵖ) P Q q hq ((linearYoneda R C).obj Y).rightOp n]
  calc ((((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            Q.complex).homologyUnop n).hom ≫
        (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
          (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop ≫
            (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
              P.complex).homologyUnop n).inv)
      = (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            Q.complex).homologyUnop n).hom ≫
        ((Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
          (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop) ≫
            (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
              P.complex).homologyUnop n).inv := by
        simp only [Category.assoc]
    _ = (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            Q.complex).homologyUnop n).hom ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) n).map
          ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).map q)).unop ≫
            (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
              P.complex).homologyUnop n).inv := by
        rw [h1]
    _ = _ := Commons.Algebra.Homology.homologyUnop_hom_naturality _ n


set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem coindIso_hom_eq {k : Type} [CommRing k] {G : Type} [Group G] (S : Subgroup G) (A : Rep.{0,0,0} k S) (n : Nat) : (groupCohomology.coindIso (k := k) (S := S) A n).hom = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (CategoryTheory.Iso.hom (CategoryTheory.Iso.trans (groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)) (NK.RepresentationTheory.GroupCohomology.lambdaIso k G S A).symm)) n) (HomologicalComplex.homologyMap (NK.RepresentationTheory.GroupCohomology.psiMap k G S A) n)) (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).inv := by
  have hkey : CategoryTheory.CategoryStruct.comp
        (((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)).isoExt n A).inv
        (((Rep.barResolution k S).isoExt n A).hom) = HomologicalComplex.homologyMap (psiMap k G S A) n :=
    isoExt_inv_comp_hom (Rep.barResolution k S)
      ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G))
      (barResChain k G S) (barResChain_π k G S) A n
  have h2 : (groupCohomologyIso A n
      ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G))).inv =
      CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (psiMap k G S A) n)
        (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).inv := by
    rw [groupCohomologyIso, groupCohomologyIsoExt, Rep.barResolution.extIso]
    rw [CategoryTheory.Iso.trans_inv, CategoryTheory.Iso.trans_inv]
    rw [CategoryTheory.Iso.symm_inv]
    rw [← CategoryTheory.Category.assoc, hkey]
  rw [groupCohomology.coindIso, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom, h2,
    CategoryTheory.Category.assoc]
  rfl


end NK.RepresentationTheory.GroupCohomology
