import Mathlib
import Submission.Work.GroupChunk.All
import Submission.Work.GroupChunk.AJ.cls_AJ0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.AJ

universe u
open CategoryTheory in
open AlgebraicGeometry in
open scoped MonObj in
open scoped AlgebraicGeometry in
theorem AJ0_pt {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [GrpObj (Work.GroupChunk.GSch D)]
    (hone : ∀ {F : Type u} [Field F] [Algebra K F],
      Work.GroupChunk.Input.cls D
        (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ η[Work.GroupChunk.GSch D]) = 0) :
    P0 ≫ Work.GroupChunk.Input.AJ₀ D = η[Work.GroupChunk.GSch D] := by
  -- The tensor unit of `Sch K` is `Spec K`, which is reduced (it is the spectrum of a field).
  have hred : AlgebraicGeometry.IsReduced
      (Over.left (MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K))) := by
    change AlgebraicGeometry.IsReduced (Spec (CommRingCat.of K))
    infer_instance
  -- Morphisms into `G D` are detected by their classes at field points of the source.
  refine Work.GroupChunk.GroupLaw.hom_ext_cls_pt (Y := MonoidalCategoryStruct.tensorUnit
    (Work.GCBasics.Sch K)) D ?_
  intro F _ _ p
  -- The class of `p ≫ P0 ≫ AJ₀` is `[p ≫ P0] - [P0]`; but `p` is the unique morphism
  -- `specOf K F ⟶ 𝟙_`, so `p ≫ P0` *is* the base point and the difference vanishes.
  have hleft : D.cls (p ≫ (P0 ≫ D.AJ₀)) = 0 := by
    rw [← Category.assoc, Work.GroupChunk.AJ.cls_AJ0 D (p ≫ P0)]
    have hp : p = Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) :=
      Work.GroupChunk.toUnit_unique p _
    have hpt : Work.SpecLin.ptDiv (p ≫ P0) = Work.GroupChunk.bcKF F D.P0Div := by
      rw [hp]; exact D.P0Div_ptDiv
    have hA0 : Work.SpecLin.ptDiv (p ≫ P0) - Work.GroupChunk.bcKF F D.P0Div = 0 :=
      sub_eq_zero.mpr hpt
    rw [← Work.GCBasics.Pic0.mk_zero, Work.GCBasics.Pic0.mk_eq_iff, hA0]
    exact Work.GCBasics.LinEquiv.refl 0
  -- The class of the unit is zero by hypothesis.
  have hright : D.cls (p ≫ η[Work.GroupChunk.GSch D]) = 0 := by
    rw [show p ≫ η[Work.GroupChunk.GSch D] =
        Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ η[Work.GroupChunk.GSch D] from by
      rw [Work.GroupChunk.toUnit_unique p _]]
    exact hone
  rw [hleft, hright]

end Work.GroupChunk.AJ
