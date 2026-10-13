import Mathlib
import Submission.Work.DSF1.Sheaf.unit_isIso_of_isZero_rightDerived

/-!
# The higher homology of `RF` at `A[0]` when `A` is `F`-acyclic

If `F : C ⤳ D` is an additive, left exact functor between abelian categories, `C` has enough
injectives, and the higher right derived functors `R^k F (A)` vanish for `k > 0`, then the object
`RF (A[0])` of the bounded below derived category of `D` is concentrated in degree `0`: its
homology in every degree `j ≠ 0` is zero.

Indeed, the unit of the right derived functor is an isomorphism at `A[0]`
(`unit_isIso_of_isZero_rightDerived`), so that `RF (A[0]) ≅ (F A)[0]`, and `(F A)[0]` is a
one-term complex sitting in degree `0`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory Limits

universe u v w x

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

theorem isZero_homology_plus_single_of_acyclic {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] (A : C)
    (h : ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero ((F.rightDerived k).obj A))
    (j : ℤ) (hj : j ≠ 0) :
    CategoryTheory.Limits.IsZero ((DerivedCategory.Plus.homologyFunctor D j).obj
      ((F.rightDerivedFunctorPlus).obj ((DerivedCategory.Plus.singleFunctor C 0).obj A))) := by
  -- the unit of the right derived functor is an isomorphism at `A[0]`
  have hη : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) :=
    unit_isIso_of_isZero_rightDerived F A h
  -- `F.mapHomotopyCategoryPlus` sends `A[0]` to `(F A)[0]`
  have eB : (F.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) ≅
      ((HomotopyCategory.Plus.singleFunctor D 0).obj (F.obj A)) :=
    ObjectProperty.isoMk (P := HomotopyCategory.plus D)
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app A))
  -- `RF (A[0]) ≅ (F A)[0]`
  have e : (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A)) ≅
      ((DerivedCategory.Plus.singleFunctor D 0).obj (F.obj A)) :=
    (asIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A))).symm ≪≫
      (DerivedCategory.Plus.Qh (C := D)).mapIso eB ≪≫ eqToIso rfl
  -- `(F A)[0]` is concentrated in degree `0`
  haveI hge : (F.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor C 0).obj A)).IsGE 0 :=
    DerivedCategory.Plus.TStructure.t.isGE_of_iso e.symm 0
  haveI hle : (F.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor C 0).obj A)).IsLE 0 :=
    DerivedCategory.Plus.TStructure.t.isLE_of_iso e.symm 0
  rcases lt_or_gt_of_ne hj with hj | hj
  · exact DerivedCategory.Plus.isZero_homology_of_isGE _
      (C := D) 0 j hj
  · exact DerivedCategory.Plus.isZero_homology_of_isLE _
      (C := D) 0 j hj

end Work.DSF1.Sheaf
