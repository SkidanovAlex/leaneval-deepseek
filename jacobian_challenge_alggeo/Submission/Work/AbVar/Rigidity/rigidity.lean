import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.Rigidity.rigid_isAlgClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.AbVar.Rigidity

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry
open scoped MonObj MonoidalCategory

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

universe u

section MonoidalAux

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {D : Type*} [Category* D] [CartesianMonoidalCategory D]

lemma muIso_hom_fst (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    (Functor.Monoidal.μIso F X Y).hom ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y) := by
  rw [Functor.Monoidal.μIso_hom]
  exact Functor.Monoidal.μ_fst F X Y

lemma muIso_hom_snd (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    (Functor.Monoidal.μIso F X Y).hom ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y) := by
  rw [Functor.Monoidal.μIso_hom]
  exact Functor.Monoidal.μ_snd F X Y

lemma muIso_inv_fst (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    (Functor.Monoidal.μIso F X Y).inv ≫ fst (F.obj X) (F.obj Y) = F.map (fst X Y) := by
  rw [← muIso_hom_fst F X Y, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma muIso_inv_snd (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    (Functor.Monoidal.μIso F X Y).inv ≫ snd (F.obj X) (F.obj Y) = F.map (snd X Y) := by
  rw [← muIso_hom_snd F X Y, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma map_fst (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    F.map (fst X Y) = (Functor.Monoidal.μIso F X Y).inv ≫ fst (F.obj X) (F.obj Y) :=
  (muIso_inv_fst F X Y).symm

lemma map_snd (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    F.map (snd X Y) = (Functor.Monoidal.μIso F X Y).inv ≫ snd (F.obj X) (F.obj Y) :=
  (muIso_inv_snd F X Y).symm

lemma map_toUnit (F : C ⥤ D) [F.Monoidal] (X : C) :
    F.map (toUnit X) = toUnit (F.obj X) ≫ (Functor.Monoidal.εIso F).hom := by
  have h : F.map (toUnit X) ≫ (Functor.Monoidal.εIso F).inv = toUnit (F.obj X) :=
    Subsingleton.elim _ _
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma map_lift (F : C ⥤ D) [F.Monoidal] {Z X Y : C} (a : Z ⟶ X) (b : Z ⟶ Y) :
    F.map (lift a b) = lift (F.map a) (F.map b) ≫ (Functor.Monoidal.μIso F X Y).hom := by
  have h : F.map (lift a b) ≫ (Functor.Monoidal.μIso F X Y).inv
      = lift (F.map a) (F.map b) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, muIso_inv_fst, ← Functor.map_comp, CartesianMonoidalCategory.lift_fst]
      exact (CartesianMonoidalCategory.lift_fst _ _).symm
    · rw [Category.assoc, muIso_inv_snd, ← Functor.map_comp, CartesianMonoidalCategory.lift_snd]
      exact (CartesianMonoidalCategory.lift_snd _ _).symm
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end MonoidalAux

/-- The base change morphism `Spec k̄ ⟶ Spec k`. -/
noncomputable def algClosureMap (k : Type u) [Field k] :
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

open CategoryTheory in
theorem rigidity {k : Type*} [Field k]
    {X Y Z : Work.AbVar.Sch k} [AlgebraicGeometry.IsProper X.hom]
    [AlgebraicGeometry.GeometricallyIntegral X.hom]
    [AlgebraicGeometry.GeometricallyIntegral Y.hom]
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
    [AlgebraicGeometry.IsSeparated Z.hom] [AlgebraicGeometry.LocallyOfFiniteType Z.hom]
    (y0 : Work.AbVar.Point Y) (f : MonoidalCategoryStruct.tensorObj X Y ⟶ Z)
    (c : Work.AbVar.Point Z)
    (hf : Work.AbVar.sectionLeft X Y y0 ≫ f = SemiCartesianMonoidalCategory.toUnit X ≫ c)
    (x0 : Work.AbVar.Point X) :
    f = SemiCartesianMonoidalCategory.snd X Y ≫ Work.AbVar.sectionRight X Y x0 ≫ f := by
  classical
  let fS := algClosureMap k
  let F := Over.pullback fS
  let X' := F.obj X
  let Y' := F.obj Y
  let Z' := F.obj Z
  let y0' : 𝟙_ (Sch (AlgebraicClosure k)) ⟶ Y' := (Functor.Monoidal.εIso F).hom ≫ F.map y0
  let x0' : 𝟙_ (Sch (AlgebraicClosure k)) ⟶ X' := (Functor.Monoidal.εIso F).hom ≫ F.map x0
  let c' : 𝟙_ (Sch (AlgebraicClosure k)) ⟶ Z' := (Functor.Monoidal.εIso F).hom ≫ F.map c
  let f' : X' ⊗ Y' ⟶ Z' := (Functor.Monoidal.μIso F X Y).hom ≫ F.map f
  -- the instances for the base changed objects
  haveI hXproper : IsProper X'.hom := by
    show IsProper (pullback.snd X.hom fS); infer_instance
  haveI hXgi : GeometricallyIntegral X'.hom := by
    show GeometricallyIntegral (pullback.snd X.hom fS); infer_instance
  haveI hYgi : GeometricallyIntegral Y'.hom := by
    show GeometricallyIntegral (pullback.snd Y.hom fS); infer_instance
  haveI hYlft : LocallyOfFiniteType Y'.hom := by
    show LocallyOfFiniteType (pullback.snd Y.hom fS); infer_instance
  haveI hZsep : IsSeparated Z'.hom := by
    show IsSeparated (pullback.snd Z.hom fS); infer_instance
  haveI hZlft : LocallyOfFiniteType Z'.hom := by
    show LocallyOfFiniteType (pullback.snd Z.hom fS); infer_instance
  -- the base changed hypothesis
  have hLiftX : lift (F.map (𝟙 X)) (F.map (SemiCartesianMonoidalCategory.toUnit X ≫ y0))
      = lift (𝟙 X') (SemiCartesianMonoidalCategory.toUnit X' ≫ y0') := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst, F.map_id]
    · rw [CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_snd, F.map_comp,
        map_toUnit F X]
      show SemiCartesianMonoidalCategory.toUnit (F.obj X)
          ≫ ((Functor.Monoidal.εIso F).hom ≫ F.map y0)
        = SemiCartesianMonoidalCategory.toUnit (F.obj X)
          ≫ ((Functor.Monoidal.εIso F).hom ≫ F.map y0)
      rfl
  have hsecLeft : F.map (Work.AbVar.sectionLeft X Y y0)
      = Work.AbVar.sectionLeft X' Y' y0' ≫ (Functor.Monoidal.μIso F X Y).hom := by
    rw [show Work.AbVar.sectionLeft X Y y0
        = lift (𝟙 X) (SemiCartesianMonoidalCategory.toUnit X ≫ y0) from rfl]
    rw [map_lift F (𝟙 X) (SemiCartesianMonoidalCategory.toUnit X ≫ y0)]
    rw [hLiftX]
    rfl
  have hf' : Work.AbVar.sectionLeft X' Y' y0' ≫ f' = SemiCartesianMonoidalCategory.toUnit X' ≫ c' := by
    have h1 : Work.AbVar.sectionLeft X' Y' y0' ≫ f'
        = F.map (Work.AbVar.sectionLeft X Y y0) ≫ F.map f := by
      show Work.AbVar.sectionLeft X' Y' y0' ≫
          ((Functor.Monoidal.μIso F X Y).hom ≫ F.map f) = _
      rw [← Category.assoc, ← hsecLeft]
    rw [h1, ← F.map_comp, hf, F.map_comp, map_toUnit F X]
    show SemiCartesianMonoidalCategory.toUnit (F.obj X)
        ≫ ((Functor.Monoidal.εIso F).hom ≫ F.map c)
      = SemiCartesianMonoidalCategory.toUnit (F.obj X)
        ≫ ((Functor.Monoidal.εIso F).hom ≫ F.map c)
    rfl
  -- the alg-closed rigidity theorem over the algebraic closure
  have key : f' = SemiCartesianMonoidalCategory.snd X' Y' ≫ Work.AbVar.sectionRight X' Y' x0' ≫ f' :=
    rigid_isAlgClosed y0' f' c' hf' x0'
  -- descend along `F`, which is faithful
  apply F.map_injective
  have hsecRight : F.map (Work.AbVar.sectionRight X Y x0)
      = Work.AbVar.sectionRight X' Y' x0' ≫ (Functor.Monoidal.μIso F X Y).hom := by
    rw [show Work.AbVar.sectionRight X Y x0
        = lift (SemiCartesianMonoidalCategory.toUnit Y ≫ x0) (𝟙 Y) from rfl]
    rw [map_lift F (SemiCartesianMonoidalCategory.toUnit Y ≫ x0) (𝟙 Y)]
    have hLiftY : lift (F.map (SemiCartesianMonoidalCategory.toUnit Y ≫ x0)) (F.map (𝟙 Y))
        = lift (SemiCartesianMonoidalCategory.toUnit Y' ≫ x0') (𝟙 Y') := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst, F.map_comp,
          map_toUnit F Y]
        show SemiCartesianMonoidalCategory.toUnit (F.obj Y)
            ≫ ((Functor.Monoidal.εIso F).hom ≫ F.map x0)
          = SemiCartesianMonoidalCategory.toUnit (F.obj Y)
            ≫ ((Functor.Monoidal.εIso F).hom ≫ F.map x0)
        rfl
      · rw [CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_snd, F.map_id]
    rw [hLiftY]
    rfl
  have hcalc : F.map (SemiCartesianMonoidalCategory.snd X Y ≫ Work.AbVar.sectionRight X Y x0 ≫ f)
      = F.map f := by
    calc F.map (SemiCartesianMonoidalCategory.snd X Y ≫ Work.AbVar.sectionRight X Y x0 ≫ f)
        = F.map (SemiCartesianMonoidalCategory.snd X Y)
            ≫ F.map (Work.AbVar.sectionRight X Y x0) ≫ F.map f := by
          rw [F.map_comp, F.map_comp]
      _ = ((Functor.Monoidal.μIso F X Y).inv ≫ snd X' Y')
            ≫ (Work.AbVar.sectionRight X' Y' x0' ≫ (Functor.Monoidal.μIso F X Y).hom)
            ≫ F.map f := by
          rw [map_snd F X Y, hsecRight]
      _ = (Functor.Monoidal.μIso F X Y).inv ≫ f' := by
          simp only [Category.assoc]
          rw [← show f' = (Functor.Monoidal.μIso F X Y).hom ≫ F.map f from rfl]
          rw [← key]
      _ = F.map f := by
          rw [show f' = (Functor.Monoidal.μIso F X Y).hom ≫ F.map f from rfl]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp]
  rw [hcalc]

end Work.AbVar.Rigidity
