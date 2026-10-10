import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Submission.Work.SSGRoute.equivHomShift_symm_cocycleMapFunctor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E0bGC

open CategoryTheory Limits

universe u v u' v'

open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false in
/-- The image under an additive functor of a cochain `K ⟶ single C q Y` is the
corresponding cochain, transported along `singleMapHomologicalComplex`. -/
private lemma cochainMapFunctor_toSingleMk_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℤ} {Y : C} {p q n : ℤ} (f : K.X p ⟶ Y) (h : p + n = q) :
    Work.SSGRoute.cochainMapFunctor F (Cochain.toSingleMk f h) =
      (Cochain.toSingleMk (F.map f) h).comp
        (Cochain.ofHom
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).inv.app Y))
        (add_zero n) := by
  apply Cochain.ext
  intro p'' q'' hpq''
  simp only [Work.SSGRoute.cochainMapFunctor_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  by_cases hp : p'' = p
  · subst hp
    have hq'' : q'' = q := by omega
    subst hq''
    rw [Cochain.toSingleMk_v (K := K) (X := Y) (f := f) (h := h) (n := n),
      Cochain.toSingleMk_v (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (X := F.obj Y) (f := F.map f) (h := h) (n := n),
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp
  · rw [Cochain.toSingleMk_v_eq_zero (K := K) (X := Y) (f := f) (h := h) (n := n)
        (p' := p'') (q' := q'') (hpq' := hpq'') hp,
      Cochain.toSingleMk_v_eq_zero (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (X := F.obj Y) (f := F.map f) (h := h) (n := n)
          (p' := p'') (q' := q'') (hpq' := hpq'') hp]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The image of `toSingleMk f` under an additive functor `F`. -/
private lemma cocycleMapFunctor_toSingleMk_GC {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℤ} {Y : C} {p q n p' : ℤ} (f : K.X p ⟶ Y) (h : p + n = q)
    (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (hf' : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d p' p ≫ F.map f = 0) :
    Work.SSGRoute.cocycleMapFunctor F (Cocycle.toSingleMk f h p' hp' hf)
      = (Cocycle.toSingleMk (F.map f) h p' hp' hf').postcomp
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).inv.app Y) := by
  apply Cocycle.ext
  change Work.SSGRoute.cochainMapFunctor F (Cochain.toSingleMk f h) =
    (Cochain.toSingleMk (F.map f) h).comp
      (Cochain.ofHom
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).inv.app Y))
      (add_zero n)
  rw [cochainMapFunctor_toSingleMk_aux]

set_option backward.isDefEq.respectTransparency false in
private theorem toSingleMk_map_aux {C : Type*} [Category* C] [Abelian C]
    {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℤ} {Y : C} {p q n : ℤ}
    (f : K.X p ⟶ Y) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p)
    (hf : K.d p' p ≫ f = 0)
    (hf'' : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d p' p ≫ F.map f = 0) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.toSingleMk (F.map f) h p' hp' hf'')
      = ShiftedHom.map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
            (CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf))
          (F.mapHomologicalComplex (ComplexShape.up ℤ))
        ≫ (shiftFunctor (CochainComplex D ℤ) n).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).hom.app Y) := by
  rw [Work.SSGRoute.equivHomShift_symm_cocycleMapFunctor F (Cocycle.toSingleMk f h p' hp' hf)]
  rw [cocycleMapFunctor_toSingleMk_GC F f h (p' := p') hp' hf hf'']
  rw [Cocycle.equivHomShift_symm_postcomp]
  rw [Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q) Y]
  have hmid := (shiftFunctor (CochainComplex D ℤ) n).map_id
      ((CochainComplex.singleFunctor D q).obj (F.obj Y))
  have h1 : Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (X := F.obj Y) (F.map f) h p' hp' hf'') ≫
        (shiftFunctor (CochainComplex D ℤ) n).map
          (𝟙 ((CochainComplex.singleFunctor D q).obj (F.obj Y))) =
      Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (X := F.obj Y) (F.map f) h p' hp' hf'') ≫ 𝟙 _ :=
    congrArg (fun t => Cocycle.equivHomShift.symm
      (Cocycle.toSingleMk (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (X := F.obj Y) (F.map f) h p' hp' hf'') ≫ t) hmid
  exact (h1.trans (Category.comp_id _)).symm

open CategoryTheory Limits in
theorem toSingleMk_map {C : Type*} [Category* C] [Abelian C]
    {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℤ} {Y : C} {p q n : ℤ}
    (f : K.X p ⟶ Y) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p)
    (hf : K.d p' p ≫ f = 0)
    (hf'' : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d p' p ≫ F.map f = 0) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.toSingleMk (F.map f) h p' hp' hf'')
      = ShiftedHom.map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
            (CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf))
          (F.mapHomologicalComplex (ComplexShape.up ℤ))
        ≫ (shiftFunctor (CochainComplex D ℤ) n).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).hom.app Y) :=
  toSingleMk_map_aux F f h p' hp' hf hf''

end Work.SSGRoute.E0bGC
