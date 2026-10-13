import Mathlib
import Submission.Work.DSF1.Sheaf.acyclicAffineHomDefs

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

/-- A faithful functor that preserves zero morphisms reflects zero objects.

Indeed, if `F.obj M` is zero then `𝟙 (F.obj M) = 0 = F.map 0`, and faithfulness
yields `𝟙 M = 0`, which characterises a zero object. -/
lemma isZero_of_isZero_obj {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] (M : C)
    (h : IsZero (F.obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact F.map_injective (by simpa using h)

/-- A sheaf of `𝒪_X`-modules is zero if and only if all of its stalks are zero.

The forgetful functor to sheaves of abelian groups is faithful and preserves zero
morphisms, so it reflects zero objects; moreover a sheaf of abelian groups is zero
exactly when all of its stalks vanish. -/
theorem isZero_iff_forall_modStalk {X : AlgebraicGeometry.Scheme.{u}}
    (N : X.Modules) :
    CategoryTheory.Limits.IsZero N ↔
      ∀ x : X, CategoryTheory.Limits.IsZero ((Work.DSF1.Sheaf.modStalk X x).obj N) := by
  constructor
  · intro h x
    have hF : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) :=
      Functor.map_isZero (SheafOfModules.toSheaf X.ringCatSheaf) h
    exact (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
      (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)).mp hF x
  · intro h
    have hF : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) :=
      (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
        (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)).mpr h
    exact isZero_of_isZero_obj (SheafOfModules.toSheaf X.ringCatSheaf) N hF

end Work.DSF1.Sheaf
