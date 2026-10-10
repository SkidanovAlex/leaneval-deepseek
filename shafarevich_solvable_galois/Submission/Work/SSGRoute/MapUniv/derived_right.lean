import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Tactic.Have
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Submission.Work.SSGRoute.MapUnivDefs
import Submission.Work.SSGRoute.phiSharp_cocycleB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "derived-right" computation

Let `F : C ⥤ D` be an exact additive functor between abelian categories, `R` a projective
resolution of `X : C`, `R'` a projective resolution of `X' : D`, and `φ : R'.complex ⟶ F(R.complex)`
a chain map compatible with the augmentations (hypothesis `hφ`).

The main result `Work.SSGRoute.MapUniv.derived_right` computes, on the derived categories, the
image under `F` of the Ext-class `R.extMk g` (as encoded by `extMkShiftedHom`), transported into
the `R'.cochainComplex` picture: it equals `R'.extMk (φ.f n ≫ F.map g)`.

Note that the augmentation compatibility hypothesis `hφ` (and the morphism `g'`) are *not* needed
for this statement: both sides only involve the chain-level data `φ`, `g`.  They are kept because
the statement is used as-is in the assembly of `mapExtAddHom_extMk_univ`.

The mathematical content is the cochain-level cocycle computation
(`Work.SSGRoute.phiSharp_cocycleB`), together with the coherence of the comparison isomorphisms
`mapDerivedCategoryFactors` (naturality in the sense of `NatTrans.CommShift`) and of the
commutation of `DerivedCategory.Q` with the shift.
-/

open CategoryTheory Limits

namespace Work.SSGRoute.MapUniv

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

section Helpers

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The degree-zero single comparison `(F.mapDerivedCategorySingleFunctor 0).hom` expressed
through `mapDerivedCategoryFactors`. -/
theorem fsi_hom_app_eq (Y : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app Y =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y) := by
  rw [← cancel_epi (F.mapDerivedCategoryFactors.inv.app
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y))]
  rw [F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  rw [Iso.inv_hom_id_app_assoc]
  rfl

/-- Naturality of `mapDerivedCategoryFactors` along `extMkShiftedHom`. -/
theorem map_naturality_extMk {X Y : C} (R : ProjectiveResolution X) {n : ℕ}
    (g : R.complex.X n ⟶ Y) (hg : R.complex.d (n+1) n ≫ g = 0) :
    ShiftedHom.map (extMkShiftedHom R g hg) (DerivedCategory.Q ⋙ F.mapDerivedCategory) ≫
      (F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y))⟦(n:ℤ)⟧'
    = F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
      ShiftedHom.map (extMkShiftedHom R g hg)
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
  have h := ShiftedHom.map_naturality (extMkShiftedHom R g hg) F.mapDerivedCategoryFactors.hom (M := ℤ)
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  exact h

/-- **The key computation.** The `F`-image of the shifted hom `extMkShiftedHom R g hg`,
expressed in the `R.cochainComplex`-picture, agrees with its image in the `R'.cochainComplex`
picture. -/
theorem key {X Y : C} (R : ProjectiveResolution X) {n : ℕ} (g : R.complex.X n ⟶ Y)
    (hg : R.complex.d (n+1) n ≫ g = 0) :
    F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map (extMkShiftedHom R g hg)) ≫
        F.mapDerivedCategory.map
          ((DerivedCategory.Q.commShiftIso (n:ℤ)).hom.app
            ((CochainComplex.singleFunctor C 0).obj Y)) ≫
        (F.mapDerivedCategory.commShiftIso (n:ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj Y) ≫
        (shiftFunctor (DerivedCategory D) (n:ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)
      = DerivedCategory.Q.map (ShiftedHom.map (extMkShiftedHom R g hg)
            (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        DerivedCategory.Q.map ((shiftFunctor (CochainComplex D ℤ) (n:ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)) ≫
        (DerivedCategory.Q.commShiftIso (n:ℤ)).hom.app
          ((CochainComplex.singleFunctor D 0).obj (F.obj Y)) := by
  have hP1' : (shiftFunctor (DerivedCategory D) (n:ℤ)).map
        ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)
      = (shiftFunctor (DerivedCategory D) (n:ℤ)).map
          (F.mapDerivedCategoryFactors.hom.app
            ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y)) ≫
        (shiftFunctor (DerivedCategory D) (n:ℤ)).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)) := by
    rw [fsi_hom_app_eq, Functor.map_comp]
  have hfold2 : F.mapDerivedCategory.map (DerivedCategory.Q.map (extMkShiftedHom R g hg)) ≫
        F.mapDerivedCategory.map
          ((DerivedCategory.Q.commShiftIso (n:ℤ)).hom.app
            ((CochainComplex.singleFunctor C 0).obj Y)) ≫
        (F.mapDerivedCategory.commShiftIso (n:ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj Y)
      = ShiftedHom.map (extMkShiftedHom R g hg)
          (DerivedCategory.Q ⋙ F.mapDerivedCategory) := by
    rw [ShiftedHom.map, Functor.commShiftIso_comp_hom_app]
    simp only [Functor.comp_map, Category.assoc]
    rfl
  have hA : ShiftedHom.map (extMkShiftedHom R g hg)
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      = DerivedCategory.Q.map (ShiftedHom.map (extMkShiftedHom R g hg)
            (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        (DerivedCategory.Q.commShiftIso (n:ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj Y)) := by
    simp only [ShiftedHom.map, Functor.commShiftIso_comp_hom_app, Functor.map_comp,
      Functor.comp_map, Category.assoc]
  have hB : (DerivedCategory.Q.commShiftIso (n:ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj Y)) ≫
        (shiftFunctor (DerivedCategory D) (n:ℤ)).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y))
      = DerivedCategory.Q.map
          ((shiftFunctor (CochainComplex D ℤ) (n:ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)) ≫
        (DerivedCategory.Q.commShiftIso (n:ℤ)).hom.app
          ((CochainComplex.singleFunctor D 0).obj (F.obj Y)) :=
    (Functor.commShiftIso_hom_naturality (F := DerivedCategory.Q)
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)
      (n:ℤ)).symm
  slice_lhs 2 4 => rw [hfold2]
  rw [hP1']
  slice_lhs 2 3 => rw [map_naturality_extMk F R g hg]
  slice_lhs 1 2 => rw [Iso.inv_hom_id_app]
  slice_lhs 1 2 => rw [Category.id_comp]
  rw [hA]
  slice_lhs 2 3 => rw [hB]

end Helpers

set_option maxHeartbeats 2000000 in
theorem derived_right {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X Y : C} (R : CategoryTheory.ProjectiveResolution X) {n : ℕ} (g : R.complex.X n ⟶ Y)
    (hg : CategoryTheory.CategoryStruct.comp (R.complex.d (n + 1) n) g = 0)
    {X' : D} (R' : CategoryTheory.ProjectiveResolution X') (g' : X' ⟶ F.obj X)
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hφ : CategoryTheory.CategoryStruct.comp φ
        (CategoryTheory.CategoryStruct.comp
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π)
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X))
        = CategoryTheory.CategoryStruct.comp R'.π ((ChainComplex.single₀ D).map g'))
    (hg' : CategoryTheory.CategoryStruct.comp (R'.complex.d (n + 1) n)
        (CategoryTheory.CategoryStruct.comp (φ.f n) (F.map g)) = 0) :
    CategoryTheory.CategoryStruct.comp
        (DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ))
        (CategoryTheory.CategoryStruct.comp
          ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
          (CategoryTheory.CategoryStruct.comp
            (F.mapDerivedCategory.map (DerivedCategory.Q.map
              (Work.SSGRoute.MapUniv.extMkShiftedHom R g hg)))
            (CategoryTheory.CategoryStruct.comp
              (F.mapDerivedCategory.map
                ((CategoryTheory.Functor.commShiftIso DerivedCategory.Q (n : ℤ)).hom.app
                  ((CochainComplex.singleFunctor C 0).obj Y)))
              (CategoryTheory.CategoryStruct.comp
                (F.mapDerivedCategory.map
                  ((CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).map
                    (CategoryTheory.CategoryStruct.id ((DerivedCategory.singleFunctor C 0).obj Y))))
                (CategoryTheory.CategoryStruct.comp
                  ((CategoryTheory.Functor.commShiftIso F.mapDerivedCategory (n : ℤ)).hom.app
                    ((DerivedCategory.singleFunctor C 0).obj Y))
                  ((CategoryTheory.shiftFunctor (DerivedCategory D) (n : ℤ)).map
                    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)))))))
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.ShiftedHom.map
            (Work.SSGRoute.MapUniv.extMkShiftedHom R'
              (CategoryTheory.CategoryStruct.comp (φ.f n) (F.map g)) hg') DerivedCategory.Q)
          ((CategoryTheory.shiftFunctor (DerivedCategory D) (n : ℤ)).map
            (CategoryTheory.CategoryStruct.id ((DerivedCategory.singleFunctor D 0).obj (F.obj Y)))) := by
  have hcocycle : Work.SSGRoute.MapUniv.phiSharp F R R' φ ≫
        ShiftedHom.map (Work.SSGRoute.MapUniv.extMkShiftedHom R g hg)
          (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
        (shiftFunctor (CochainComplex D ℤ) (n:ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Y)
      = Work.SSGRoute.MapUniv.extMkShiftedHom R' (φ.f n ≫ F.map g) hg' :=
    Work.SSGRoute.phiSharp_cocycleB F R g hg R' φ hg'
  have hkey := key F R g hg
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [hkey]
  slice_lhs 1 3 => rw [← CategoryTheory.Functor.map_comp]
  slice_lhs 1 2 => rw [← CategoryTheory.Functor.map_comp]
  rw [hcocycle]
  rw [ShiftedHom.map]

end Work.SSGRoute.MapUniv
