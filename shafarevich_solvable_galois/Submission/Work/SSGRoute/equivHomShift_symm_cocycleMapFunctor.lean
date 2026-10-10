import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Submission.Work.SSGRoute.cocycleMapFunctor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Limits

universe u v u' v'

set_option backward.isDefEq.respectTransparency false in
theorem equivHomShift_symm_cocycleMapFunctor {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cocycle K L n) :
    ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
      = CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (Work.SSGRoute.cocycleMapFunctor F z) := by
  rw [ShiftedHom.map, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
      CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply]
  ext i
  simp only [HomologicalComplex.comp_f,
    CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe,
    CochainComplex.HomComplex.Cochain.rightShift_v,
    Work.SSGRoute.cocycleMapFunctor_coe,
    Work.SSGRoute.cochainMapFunctor_v,
    CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CategoryTheory.Functor.mapHomologicalComplex_map_f,
    CategoryTheory.Functor.map_comp,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
  simp

end Work.SSGRoute
