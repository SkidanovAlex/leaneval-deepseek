import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear.FunctionFieldPoint
import Submission.Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap_of_not_isClosed
import Submission.Work.SpecLin.Points.ptDiv_deg
import Submission.Work.CurveBasics.Point.coheight_eq_one_of_isClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Curve

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem exists_place_genericPoint {k : Type u} [Field k] (C : Curve k) :
    ∃ Q : (C.baseChange (C.functionField : Type u)).Place,
      Q.degree = 1 ∧
      (∀ f : C.functionField, f ≠ 0 →
        (C.baseChange (C.functionField : Type u)).ordAt
          ((Curve.bcSquare C (C.functionField : Type u)).fieldMap.hom f) Q = 0) ∧
      (¬ IsClosed ({(C.baseChangeFst (C.functionField : Type u)) Q.point} : Set C.left)) := by
  classical
  -- The generic point of `C`, as a `K(C)`-valued point of `C` over `k`.
  let p : Work.SpecLin.CurveFPt C (C.functionField : Type u) :=
    Over.homMk (C.left.fromSpecStalk (genericPoint C.left))
      (Work.CurveBasics.Curve.fromSpecStalk_genericPoint_comp_hom C)
  -- its image in `C` is the generic point, which is not closed
  have hbase : (C.baseChangeFst (C.functionField : Type u)) (Work.SpecLin.ptToPoint p)
      = (C.left.fromSpecStalk (genericPoint C.left))
          (IsLocalRing.closedPoint ↥(C.left.presheaf.stalk (genericPoint C.left))) := by
    rw [Work.SpecLin.ptToPoint]
    exact congrArg (fun g => g (IsLocalRing.closedPoint (C.functionField : Type u)))
      (Work.SpecLin.ptLeft_fst p)
  have hpt : (C.baseChangeFst (C.functionField : Type u))
      (Work.SpecLin.ptPlace p).point = genericPoint C.left := by
    show (C.baseChangeFst (C.functionField : Type u))
        (Work.SpecLin.ptToPoint p) = genericPoint C.left
    rw [hbase]
    exact Scheme.fromSpecStalk_closedPoint
  have hnotclosed :
      ¬ IsClosed ((singleton ((C.baseChangeFst (C.functionField : Type u))
        (Work.SpecLin.ptPlace p).point)) : Set C.left) := by
    rw [hpt]
    intro hc
    have h1 : Order.coheight (genericPoint C.left) = 1 :=
      Point.coheight_eq_one_of_isClosed C hc
    rw [coheight_genericPoint C] at h1
    exact one_ne_zero h1.symm
  refine ⟨Work.SpecLin.ptPlace p, ?_, ?_, hnotclosed⟩
  · -- its residue field is `F`, so it has degree one
    show (C.baseChange (C.functionField : Type u)).hom.residueDegree
        (Work.SpecLin.ptToPoint p) = 1
    exact Work.SpecLin.Points.residueDegree_of_section (Work.SpecLin.ptLeft p)
      (C.baseChange (C.functionField : Type u)).hom
      (Work.SpecLin.Points.ptLeft_comp_hom p)
      (IsLocalRing.closedPoint (C.functionField : Type u))
  · intro f hf
    exact BCSquare.ordAt_fieldMap_of_not_isClosed (bcSquare C (C.functionField : Type u))
      (Work.SpecLin.ptPlace p) hnotclosed hf

end Work.CurveBasics.Curve
