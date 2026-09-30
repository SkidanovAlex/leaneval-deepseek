import Mathlib
import Submission.Work.GroupChunk.Interface
import Submission.Work.Universal.Basic
import Submission.Work.SpecLin.Points.ptDiv_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory

namespace Work.JacFinal

theorem genus_zero_no_input {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {P0 : CategoryTheory.MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch k) ⟶ C.toOver} [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) (hg : D.g = 0) {F : Type u} [Field F] [Algebra k F] (x : Work.GCBasics.FPt C.toOver F) : False := by
  have hdeg1 : Work.GCBasics.Ddeg C F (D.divOf D.g (x ≫ D.curveAdd)) = (D.g : ℤ) :=
    (D.symGeom D.g).divOf_deg (x ≫ D.curveAdd)
  have hpt : Work.GCBasics.Ddeg C F (Work.SpecLin.ptDiv x) = 1 :=
    Work.SpecLin.Points.ptDiv_deg x
  have hEq : D.divOf D.g (x ≫ D.curveAdd)
      = Work.SpecLin.ptDiv x + (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div :=
    D.curveAdd_divOf x
  have hA : Work.GCBasics.Ddeg C F
      (Work.SpecLin.ptDiv x + (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div) = (D.g : ℤ) := by
    rw [← hEq]; exact hdeg1
  have hz : (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div = 0 := by
    rw [hg, Nat.zero_sub, zero_nsmul]
  rw [hz, add_zero, hpt, hg] at hA
  omega

end Work.JacFinal
