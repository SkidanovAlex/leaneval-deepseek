import Mathlib
import Submission.Work.SSGRoute.MapExtAuxDefs
import Submission.Work.SSGRoute.ExtendFunctorIso
import Submission.Work.SSGRoute.phiSharp_f
import Submission.Work.SSGRoute.cocycleMapFunctor
import Submission.Work.SSGRoute.equivHomShift_symm_cocycleMapFunctor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Limits
open CochainComplex.HomComplex

section HelperA

/-- The degree-`j` component of `(singleMapHomologicalComplex F _ j).inv.app X`. -/
private lemma singleMapHomologicalComplex_inv_app_f_selfB
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {X : C} (j : ℤ) :
    (((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) j).inv.app X).f j) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j (F.obj X)).hom ≫
        F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j X).inv :=
  HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (ComplexShape.up ℤ) j X

set_option backward.isDefEq.respectTransparency false in
/-- The image under an additive functor of the cochain `K.X p ⟶ single X` of a single complex. -/
private lemma cochainMapFunctor_toSingleMkB
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℤ} {X : C} {p q n : ℤ} (f : K.X p ⟶ X) (h : p + n = q) :
    cochainMapFunctor F (Cochain.toSingleMk f h) =
      (Cochain.toSingleMk (F.map f) h).comp
        (Cochain.ofHom
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).inv.app X))
        (add_zero n) := by
  apply Cochain.ext
  intro p'' q'' hpq''
  simp only [cochainMapFunctor_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  by_cases hp : p'' = p
  · subst hp
    have hq'' : q'' = q := by omega
    subst hq''
    rw [Cochain.toSingleMk_v (K := K) (X := X) (f := f) (h := h) (n := n),
      Cochain.toSingleMk_v (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (X := F.obj X) (f := F.map f) (h := h) (n := n),
      singleMapHomologicalComplex_inv_app_f_selfB F q'']
    simp
  · rw [Cochain.toSingleMk_v_eq_zero (K := K) (X := X) (f := f) (h := h) (n := n)
        (p' := p'') (q' := q'') (hpq' := hpq'') hp,
      Cochain.toSingleMk_v_eq_zero (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (X := F.obj X) (f := F.map f) (h := h) (n := n)
          (p' := p'') (q' := q'') (hpq' := hpq'') hp]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- `cocycleMapFunctor F` of the cocycle associated to a single complex, expressed using
`HomologicalComplex.singleMapHomologicalComplex`. -/
private lemma cocycleMapFunctor_toSingleMkB
    {C : Type*} [Category C] [Abelian C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℤ} {X : C} {p q n : ℤ} (f : K.X p ⟶ X) (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (hf' : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d p' p ≫ F.map f = 0) :
    cocycleMapFunctor F (Cocycle.toSingleMk f h p' hp' hf)
      = (Cocycle.toSingleMk (F.map f) h p' hp' hf').postcomp
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).inv.app X) := by
  apply Cocycle.ext
  change cochainMapFunctor F (Cochain.toSingleMk f h) =
    (Cochain.toSingleMk (F.map f) h).comp
      (Cochain.ofHom
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).inv.app X))
      (add_zero n)
  rw [cochainMapFunctor_toSingleMkB]

end HelperA

section PostcompAux
variable {C : Type*} [Category C] [Preadditive C]

private lemma cocycle_postcomp_postcomp {K L M N : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) (f : L ⟶ M) (g : M ⟶ N) :
    (z.postcomp f).postcomp g = z.postcomp (f ≫ g) := by
  apply Cocycle.ext
  simp only [Cocycle.postcomp_coe, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.ofHom_comp]

private lemma cocycle_postcomp_id {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    z.postcomp (𝟙 L) = z := by
  apply Cocycle.ext
  simp only [Cocycle.postcomp_coe, Cochain.comp_id]

end PostcompAux

set_option backward.isDefEq.respectTransparency false in
theorem phiSharp_cocycleB {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    {X Y : C} (R : CategoryTheory.ProjectiveResolution X) {n : ℕ} (g : R.complex.X n ⟶ Y)
    (hg : CategoryTheory.CategoryStruct.comp (R.complex.d (n+1) n) g = 0)
    {X' : D} (R' : CategoryTheory.ProjectiveResolution X')
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hg' : CategoryTheory.CategoryStruct.comp (R'.complex.d (n+1) n)
        (CategoryTheory.CategoryStruct.comp (φ.f n) (F.map g)) = 0) :
    CategoryTheory.CategoryStruct.comp (Work.SSGRoute.phiSharp F R R' φ)
      (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.ShiftedHom.map (Work.SSGRoute.extMkShiftedHom R g hg)
          (F.mapHomologicalComplex (ComplexShape.up ℤ)))
        ((CategoryTheory.shiftFunctor (CochainComplex D ℤ) (n : ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)))
      = Work.SSGRoute.extMkShiftedHom R' (CategoryTheory.CategoryStruct.comp (φ.f n) (F.map g)) hg' := by
  simp only [Work.SSGRoute.extMkShiftedHom]
  rw [equivHomShift_symm_cocycleMapFunctor F]
  apply Cocycle.equivHomShift.injective
  rw [Cocycle.equivHomShift_comp, Cocycle.equivHomShift_comp_shift]
  rw [AddEquiv.apply_symm_apply]
  have hmap : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).d
        (-↑(n+1)) (-↑n) ≫
      F.map ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) = 0 := by
    have h1 : R.cochainComplex.d (-↑(n+1)) (-↑n) ≫
        ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) = 0 := by
      simpa [R.cochainComplex_d (-(↑n+1)) (-↑n) (n+1) n (by simp) rfl, hg]
    rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, h1, Functor.map_zero]
  erw [cocycleMapFunctor_toSingleMkB F ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) (by simp)
    (-↑(n+1)) (by lia)
    (by simpa [R.cochainComplex_d (-(↑n+1)) (-↑n) (n+1) n (by simp) rfl, hg]) hmap]
  erw [cocycle_postcomp_postcomp]
  erw [show (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app Y ≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y
      = 𝟙 _ from Iso.inv_hom_id_app
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0) Y]
  erw [cocycle_postcomp_id]
  erw [AddEquiv.apply_symm_apply]
  apply Cocycle.ext
  erw [Cocycle.precomp_coe, Cocycle.toSingleMk_coe]
  erw [← Cochain.toSingleMk_precomp]
  erw [Functor.map_comp]
  have hcomp : (phiSharp F R R' φ).f (-↑n) ≫
      (F.map ((R.cochainComplexXIso (-↑n) n rfl).hom) ≫ F.map g)
      = (R'.cochainComplexXIso (-↑n) n rfl).hom ≫ (φ.f n ≫ F.map g) := by
    rw [← Category.assoc, phiSharp_f F R R' φ n, Category.assoc]
  erw [hcomp]
  rfl

end Work.SSGRoute
