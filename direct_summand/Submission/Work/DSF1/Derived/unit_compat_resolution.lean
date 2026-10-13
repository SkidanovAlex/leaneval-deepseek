import Mathlib
import Submission.Work.DSG1.rdfpuBridge
import Submission.Work.DSF1.Sheaf.AcyclicToolkit

namespace Work.DSF1.Derived

open CategoryTheory

universe u v w x

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem unit_compat_resolution {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C] [HasDerivedCategory C] {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D] [HasDerivedCategory D] (F : CategoryTheory.Functor C D) [CategoryTheory.Functor.Additive F] [CategoryTheory.EnoughInjectives C] (M : C) (K : CochainComplex.Plus C) (q : Work.DSF1.Sheaf.singlePlusObj C M ⟶ K) (hunit : CategoryTheory.IsIso (F.rightDerivedFunctorPlusUnit.app K)) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0).app M) (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q).map q))) (CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app K)) = CategoryTheory.CategoryStruct.comp ((DerivedCategory.Plus.Q.mapIso ((Work.DSG1.mapSinglePlusIso F M).symm)).hom) ((DerivedCategory.Plus.Q).map ((F.mapCochainComplexPlus).map q)) := by
  haveI := hunit
  have key : (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0).app M =
      (DerivedCategory.Plus.Q).map ((Work.DSG1.mapSinglePlusIso F M).inv) ≫ F.rightDerivedFunctorPlusUnit.app (Work.DSG1.singlePlusObj C M) := by
    rw [Work.DSG1.rdfpuBridge F M]
    rw [Work.DSG1.singlePlusIso_eq_refl (C := D) (F.obj M),
        Work.DSG1.singlePlusIso_eq_refl (C := C) M]
    erw [CategoryTheory.Iso.refl_hom]
    erw [CategoryTheory.Category.id_comp]
    erw [CategoryTheory.Iso.refl_inv]
    erw [CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Category.comp_id]
  rw [key]
  simp only [CategoryTheory.Category.assoc]
  erw [← CategoryTheory.NatTrans.naturality_assoc F.rightDerivedFunctorPlusUnit q]
  simp only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Iso.symm_hom]
  rw [CategoryTheory.Functor.comp_map]
  erw [CategoryTheory.IsIso.hom_inv_id]
  erw [CategoryTheory.Category.comp_id]

end Work.DSF1.Derived
