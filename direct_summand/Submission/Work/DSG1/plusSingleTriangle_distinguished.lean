import Mathlib

open CategoryTheory
open CategoryTheory.Pretriangulated

-- The statement involves `DerivedCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.ι`
-- and `DerivedCategory.singleFunctor C 0` (which are equal through the isomorphism
-- `DerivedCategory.Plus.singleFunctorιIso C 0 = Iso.refl _`); the tactic proofs below
-- compare objects of `DerivedCategory C` that are equal only through this identification.
set_option backward.isDefEq.respectTransparency false

namespace Work.DSG1

universe u v

/-- The distinguished triangle in the bounded-below derived category associated with a short
exact short complex, between the single objects.

Suggested proof: let `T` be the triangle in `DerivedCategory.Plus C` with first two morphisms
`(DerivedCategory.Plus.singleFunctor C 0).map S.f` and `... .map S.g` and whose third morphism is
the preimage under the fully faithful `DerivedCategory.Plus.ι` of
`hS.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso 1).inv.app _` (exactly the pattern of
`ShortComplex.ShortExact.boundedSingleTriangle` in TauCeti's
`Algebra/Homology/DerivedCategory/Bounded.lean`, using
`DerivedCategory.Plus.singleFunctorιIso (C := C) 0 = Iso.refl _`).  Then
`DerivedCategory.Plus.ι.mapTriangle.obj T ≅ hS.singleTriangle` by `Triangle.isoMk` with
`Iso.refl`s, and `T` is distinguished by
`← CategoryTheory.Functor.map_distinguished_iff (DerivedCategory.Plus.ι)` and
`isomorphic_distinguished`. -/
theorem plusSingleTriangle_distinguished {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory C]
    {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    ∃ δ : (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory.Plus C) 1).obj
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
        ((DerivedCategory.Plus.singleFunctor C 0).map S.g) δ ∈
        CategoryTheory.Pretriangulated.distinguishedTriangles := by
  -- The third morphism `δ` is the preimage under the fully faithful inclusion
  -- `DerivedCategory.Plus.ι` of `hS.singleδ` suitably shifted into `Plus C`.
  let δ : (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
      (CategoryTheory.shiftFunctor (DerivedCategory.Plus C) (1 : ℤ)).obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) :=
    DerivedCategory.Plus.ι.preimage (hS.singleδ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))
  have hδ : DerivedCategory.Plus.ι.map δ = hS.singleδ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) :=
    DerivedCategory.Plus.ι.map_preimage _
  refine ⟨δ, ?_⟩
  -- `Plus C` is pretriangulated as a full subcategory of `DerivedCategory C`, so it
  -- suffices to exhibit an isomorphism of `DerivedCategory.Plus.ι.mapTriangle.obj T`
  -- with the (distinguished) triangle `hS.singleTriangle`.
  refine (CategoryTheory.Functor.map_distinguished_iff (DerivedCategory.Plus.ι) _).mp ?_
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · show (DerivedCategory.singleFunctor C 0).map S.f ≫ 𝟙 _ = 𝟙 _ ≫
      (DerivedCategory.singleFunctor C 0).map S.f
    rw [Category.id_comp, Category.comp_id]
  · show (DerivedCategory.singleFunctor C 0).map S.g ≫ 𝟙 _ = 𝟙 _ ≫
      (DerivedCategory.singleFunctor C 0).map S.g
    rw [Category.id_comp, Category.comp_id]
  · simp only [Functor.mapTriangle_obj, Triangle.mk_mor₃, Triangle.mk_obj₁,
      Triangle.mk_obj₃, Iso.refl_hom]
    rw [hδ]
    simp
    exact Category.comp_id hS.singleδ

end Work.DSG1
