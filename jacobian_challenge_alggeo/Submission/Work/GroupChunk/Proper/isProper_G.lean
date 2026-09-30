import Mathlib
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.Group

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.GroupChunk.Proper

universe u
open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem isProper_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [IsSeparated (Work.GroupChunk.GSch D).hom]
    [LocallyOfFiniteType (Work.GroupChunk.GSch D).hom] :
    IsProper (Work.GroupChunk.GSch D).hom := by
  haveI : Work.GroupChunk.Input C P0 := D
  haveI hUC : UniversallyClosed (Work.GroupChunk.GSch D).hom := by
    haveI hsurj : Surjective (D.AJSym).left := ⟨Work.GroupChunk.Input.AJSym_surjective D⟩
    have hcomp : (D.AJSym).left ≫ (Work.GroupChunk.GSch D).hom = (D.Sym D.g).hom :=
      Over.w D.AJSym
    haveI : UniversallyClosed ((D.AJSym).left ≫ (Work.GroupChunk.GSch D).hom) := by
      rw [hcomp]
      infer_instance
    exact UniversallyClosed.of_comp_surjective (D.AJSym).left (Work.GroupChunk.GSch D).hom
  exact IsProper.mk

end Work.GroupChunk.Proper
