import Mathlib
import Submission.Work.SSGRoute.MapUnivDefs
import Submission.Work.SSGRoute.MapUniv.phiSharp_augmentation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The left-hand side comparison for the universal `Ext` map (`v2`)

Let `F : C ⥤ D` be an additive functor between abelian categories preserving finite limits
and finite colimits, `R` a projective resolution of `X : C`, `R'` a projective resolution of
`X' : D` and `g' : X' ⟶ F.obj X`.  Given a chain map `φ : R'.complex ⟶ F(R.complex)`
compatible with the augmentations (`hφ`), the induced cochain map
`phiSharp F R R' φ : R'.cochainComplex ⟶ F(R.cochainComplex)` is compatible with the
integer indexed augmentations `R'.π'` and `R.π'`
(`phiSharp_augmentation`).  Passing to the derived category, we obtain the identity
proved here:

`g'` transported to the derived category via `singleFunctor D 0` and
`mapDerivedCategorySingleFunctor` agrees with the morphism obtained by dividing
`Q(phiSharp F R R' φ)` by the quasi-isomorphisms `Q(R'.π')` and `Q(R.π')`
(via `mapDerivedCategoryFactors`).

The proof is a formal consequence of three compatibilities:

* `phiSharp_augmentation` (the chain level statement of `hφ` after applying `phiSharp`),
* the naturality of the isomorphism `F.mapDerivedCategoryFactors` at `R.π'`,
* the identification of `Q(singleMapHomologicalComplex F (up ℤ) 0).hom ≫
  (F.mapDerivedCategorySingleFunctor 0).inv` with `F.mapDerivedCategoryFactors.inv`
  (`mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`).

The `set_option` below is needed for the same reason as in `phiSharp_augmentation`: several
objects are only propositionally equal after unfolding the (large) definitions of
`DerivedCategory.singleFunctor` and `CochainComplex.singleFunctor`.
-/

open CategoryTheory Limits

namespace Work.SSGRoute.MapUniv

set_option backward.isDefEq.respectTransparency false in
theorem derived_left_v2 {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X : C} (R : CategoryTheory.ProjectiveResolution X)
    {X' : D} (R' : CategoryTheory.ProjectiveResolution X') (g' : X' ⟶ F.obj X)
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hφ : CategoryTheory.CategoryStruct.comp φ
        (CategoryTheory.CategoryStruct.comp
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π)
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X))
        = CategoryTheory.CategoryStruct.comp R'.π ((ChainComplex.single₀ D).map g')) :
    CategoryTheory.CategoryStruct.comp ((DerivedCategory.singleFunctor D 0).map g')
        ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
      = CategoryTheory.CategoryStruct.comp (CategoryTheory.inv (DerivedCategory.Q.map R'.π'))
          (CategoryTheory.CategoryStruct.comp
            (DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ))
            (CategoryTheory.CategoryStruct.comp
              ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
              (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')))) := by
  -- The chain level identity provided by the hypothesis `hφ`.
  have hφ' := Work.SSGRoute.MapUniv.phiSharp_augmentation F R R' g' φ hφ
  -- Naturality of `F.mapDerivedCategoryFactors.inv` at the augmentation `R.π'`.
  have hnat := NatTrans.naturality F.mapDerivedCategoryFactors.inv R.π'
  -- The degree `0` computation identifying `Q(singleMapHomologicalComplex F (up ℤ) 0).hom`
  -- with `F.mapDerivedCategoryFactors.inv` after inverting `mapDerivedCategorySingleFunctor`.
  have hkey : DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app X =
      F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) := by
    erw [← CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      F X, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    try rfl
  -- The main computation, after multiplying on the left by the (invertible) `Q.map R'.π'`.
  have hmain2 : DerivedCategory.Q.map R'.π' ≫
        ((DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X)
      = DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ) ≫
        (F.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
          (DerivedCategory.Q ⋙ F.mapDerivedCategory).map R.π') := by
    change DerivedCategory.Q.map R'.π' ≫
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map g') ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app X) = _
    rw [← DerivedCategory.Q.map_comp_assoc]
    rw [← hφ']
    rw [DerivedCategory.Q.map_comp_assoc, DerivedCategory.Q.map_comp_assoc]
    rw [hkey]
    rw [← Functor.comp_map]
    erw [← hnat]
  -- Assemble: `Q.map R'.π'` is invertible, and cancel it on the left.
  rw [← IsIso.inv_hom_id_assoc (DerivedCategory.Q.map R'.π')
    ((DerivedCategory.singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X)]
  rw [hmain2]
  erw [Functor.comp_map]

end Work.SSGRoute.MapUniv
