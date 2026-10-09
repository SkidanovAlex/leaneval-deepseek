import Mathlib
import Submission.Work.SSGRoute.MapUnivDefs
import Submission.Work.SSGRoute.MapUniv.phiSharp_augmentation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Limits

/-!
# Functoriality of the augmentation on the left (the "derived-left" computation)

For an exact additive functor `F : C ⥤ D` between abelian categories, projective resolutions
`R` of `X : C` and `R'` of `X' : D`, and a chain-level lift `φ : R'.complex ⟶ F(R.complex)`
compatible with the augmentations (`hφ`), the cochain-level lift `phiSharp` induces, on the
derived categories, the equality

`(singleFunctor D 0).map g' ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app X
   = inv (Q.map R'.π') ≫ Q.map (phiSharp F R R' φ)
       ≫ (F.mapDerivedCategoryFactors).inv.app R.cochainComplex
       ≫ F.mapDerivedCategory.map (Q.map R.π')`.

The mathematical content is the augmentation compatibility of `phiSharp`
(`Work.SSGRoute.MapUniv.phiSharp_augmentation`), transported to the derived category: applying
`Q` to that identity, cancelling the naturality square of `F.mapDerivedCategoryFactors` against
`R.π'`, and finally cancelling the isomorphism `(F.mapDerivedCategorySingleFunctor 0).hom.app X`
(whose inverse is what appears on the left-hand side).

The requested statement refers to the identifier `ChainChainComplex.single₀`, which is not a
name in Mathlib; `ChainComplex.single₀` is meant (compare the identical hypothesis in
`phiSharp_augmentation`).  To leave the requested statement *literally* unchanged, the alias
below is provided, so that the statement elaborates exactly as written while denoting
`ChainComplex.single₀`.
-/

/- Alias making the identifier `ChainChainComplex.single₀` of the requested statement resolve to
`ChainComplex.single₀` (the intended name). -/
namespace ChainChainComplex
noncomputable abbrev single₀ := ChainComplex.single₀
end ChainChainComplex

namespace Work.SSGRoute.MapUniv

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false in
theorem derived_left {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
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
        = CategoryTheory.CategoryStruct.comp R'.π ((ChainChainComplex.single₀ D).map g')) :
    CategoryTheory.CategoryStruct.comp ((DerivedCategory.singleFunctor D 0).map g')
        ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
      = CategoryTheory.CategoryStruct.comp (CategoryTheory.inv (DerivedCategory.Q.map R'.π'))
          (CategoryTheory.CategoryStruct.comp
            (DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ))
            (CategoryTheory.CategoryStruct.comp
              ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
              (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')))) := by
  -- (A) Augmentation compatibility of `phiSharp`, transported to the derived category.
  have hA : CategoryTheory.CategoryStruct.comp
        (DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ))
        (CategoryTheory.CategoryStruct.comp
          (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π'))
          (DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X)))
      = CategoryTheory.CategoryStruct.comp (DerivedCategory.Q.map R'.π')
          ((DerivedCategory.singleFunctor D 0).map g') := by
    have h := congrArg DerivedCategory.Q.map
      (Work.SSGRoute.MapUniv.phiSharp_augmentation F R R' g' φ hφ)
    simp only [Functor.map_comp] at h
    rw [show DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map g')
          = (DerivedCategory.singleFunctor D 0).map g' from rfl] at h
    exact h
  -- (B) The degree-zero `single` comparison is the naturality of `mapDerivedCategoryFactors`.
  have hB : CategoryTheory.CategoryStruct.comp
        ((F.mapDerivedCategoryFactors).inv.app ((CochainComplex.singleFunctor C 0).obj X))
        ((F.mapDerivedCategorySingleFunctor 0).hom.app X)
      = DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) := by
    exact F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X
  -- (C) Naturality of `F.mapDerivedCategoryFactors.inv` against `R.π'`.
  have hC : CategoryTheory.CategoryStruct.comp
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π'))
        ((F.mapDerivedCategoryFactors).inv.app ((CochainComplex.singleFunctor C 0).obj X))
      = CategoryTheory.CategoryStruct.comp
          ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
          (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')) := by
    have h := F.mapDerivedCategoryFactors.inv.naturality R.π'
    simpa only [Functor.comp_map] using h
  -- (D) The same identity after inserting the inverse single comparison on the left.
  have hD : CategoryTheory.CategoryStruct.comp
        (DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ))
        (CategoryTheory.CategoryStruct.comp
          ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
          (CategoryTheory.CategoryStruct.comp
            (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π'))
            ((F.mapDerivedCategorySingleFunctor 0).hom.app X)))
      = CategoryTheory.CategoryStruct.comp (DerivedCategory.Q.map R'.π')
          ((DerivedCategory.singleFunctor D 0).map g') := by
    rw [← Category.assoc ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
            (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π'))
            ((F.mapDerivedCategorySingleFunctor 0).hom.app X),
        ← hC, Category.assoc, hB]
    exact hA
  have keyl : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp ((DerivedCategory.singleFunctor D 0).map g')
          ((F.mapDerivedCategorySingleFunctor 0).inv.app X))
        ((F.mapDerivedCategorySingleFunctor 0).hom.app X)
      = (DerivedCategory.singleFunctor D 0).map g' := by
    simp
  have keyr : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp (CategoryTheory.inv (DerivedCategory.Q.map R'.π'))
          (CategoryTheory.CategoryStruct.comp
            (DerivedCategory.Q.map (Work.SSGRoute.MapUniv.phiSharp F R R' φ))
            (CategoryTheory.CategoryStruct.comp
              ((F.mapDerivedCategoryFactors).inv.app R.cochainComplex)
              (F.mapDerivedCategory.map (DerivedCategory.Q.map R.π')))))
        ((F.mapDerivedCategorySingleFunctor 0).hom.app X)
      = (DerivedCategory.singleFunctor D 0).map g' := by
    simp only [Category.assoc]
    rw [hD, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← cancel_mono ((F.mapDerivedCategorySingleFunctor 0).hom.app X)]
  exact keyl.trans keyr.symm

end Work.SSGRoute.MapUniv
