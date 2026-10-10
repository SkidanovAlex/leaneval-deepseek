import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Tactic.Have
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.MapUniv.derived_left_v2
import Submission.Work.SSGRoute.MapUniv.derived_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Limits

namespace Work.SSGRoute

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem mapExtAddHom_extMk_univ {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian D]
    [CategoryTheory.HasExt D]
    (F : CategoryTheory.Functor C D) [CategoryTheory.Functor.Additive F]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X Y : C} (R : CategoryTheory.ProjectiveResolution X) {n : ℕ} (g : R.complex.X n ⟶ Y)
    (hg : CategoryTheory.CategoryStruct.comp (R.complex.d (n + 1) n) g = 0)
    {X' : D} (R' : CategoryTheory.ProjectiveResolution X') (g' : X' ⟶ F.obj X)
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hφ : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp φ
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π))
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X)
        = CategoryTheory.CategoryStruct.comp R'.π ((ChainComplex.single₀ D).map g'))
    (hg' : CategoryTheory.CategoryStruct.comp (R'.complex.d (n + 1) n)
        (CategoryTheory.CategoryStruct.comp (φ.f n) (F.map g)) = 0) :
    (CategoryTheory.Abelian.Ext.mk₀ g').comp
        ((R.extMk g (n + 1) rfl hg).mapExactFunctor F) (zero_add n)
      = R'.extMk (CategoryTheory.CategoryStruct.comp (φ.f n) (F.map g)) (n + 1) rfl hg' := by
  have := HasDerivedCategory.standard C
  have := HasDerivedCategory.standard D
  have hφ' : φ ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π ≫
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X
      = R'.π ≫ (ChainComplex.single₀ D).map g' := by
    rw [← Category.assoc]; exact hφ
  ext
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.mk₀_hom]
  rw [ShiftedHom.mk₀_comp]
  rw [ProjectiveResolution.extMk_hom]
  rw [ProjectiveResolution.extMk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp]
  simp only [ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.comp_map,
    ShiftedHom.comp_mk₀_id, ShiftedHom.mk₀_id_comp, ShiftedHom.mk₀_comp_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Functor.map_id, Category.id_comp,
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  simp only [ShiftedHom.map, Functor.map_comp, Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.commShiftIso_hom_naturality_assoc, Functor.map_inv]
  conv_lhs => rw [← Category.assoc]
  rw [Work.SSGRoute.MapUniv.derived_left_v2 F R R' g' φ hφ']
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [cancel_epi (CategoryTheory.inv (DerivedCategory.Q.map R'.π'))]
  have hR := Work.SSGRoute.MapUniv.derived_right F R g hg R' g' φ hφ' hg'
  simp only [Work.SSGRoute.MapUniv.extMkShiftedHom, ShiftedHom.map, Category.assoc] at hR
  exact hR

end Work.SSGRoute
