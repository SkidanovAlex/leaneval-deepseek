import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.P1.const_of_action
import Submission.Work.AbVar.ProjectiveLine.chart
import Submission.Work.AbVar.ProjectiveLine.isProper_P1
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.AbVar.P1Action.Action
import Submission.Work.AbVar.P1Action.Points
import Submission.Work.AbVar.P1Action.gmToP1_dominant
import Submission.Work.AbVar.P1Action.gmToP1_sectionLeft
import Submission.Work.AbVar.P1Action.ChartGeo
import Submission.Work.AbVar.P1Action.scalingAct_fixed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.AbVar.ProjectiveLine

open CategoryTheory AlgebraicGeometry MonObj in
open scoped MonoidalCategory in
/-- The orbit map `𝔾_m ⟶ ℙ¹` is equivariant for the scaling action. -/
theorem scalingActionData_equivariance (k : Type*) [Field k] :
    MonoidalCategoryStruct.tensorHom (Work.AbVar.P1Action.gmToP1 k) (𝟙 (Work.AbVar.Gm k))
        ≫ Work.AbVar.P1Action.scalingAct k
      = MonObj.mul ≫ Work.AbVar.P1Action.gmToP1 k :=
  Work.AbVar.P1Action.scalingAct_equivariance_aux k

open CategoryTheory AlgebraicGeometry MonObj in
open scoped MonoidalCategory in
/-- The point `∞ = [1 : 0]` is fixed by the scaling action. -/
theorem scalingActionData_fixed (k : Type*) [Field k] :
    Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (Work.AbVar.P1Action.pointInf k)
        ≫ Work.AbVar.P1Action.scalingAct k
      = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ Work.AbVar.P1Action.pointInf k :=
  Work.AbVar.P1Action.scalingAct_fixed k

open CategoryTheory AlgebraicGeometry MonObj in
open scoped MonoidalCategory in
theorem scalingActionData (k : Type*) [Field k] :
    ∃ (act : Work.AbVar.P1 k ⊗ Work.AbVar.Gm k ⟶ Work.AbVar.P1 k)
      (x0 : Work.AbVar.Point (Work.AbVar.P1 k)) (j : Work.AbVar.Gm k ⟶ Work.AbVar.P1 k),
      (Work.AbVar.sectionLeft (Work.AbVar.P1 k) (Work.AbVar.Gm k)
          (MonObj.one (X := Work.AbVar.Gm k)) ≫ act = 𝟙 (Work.AbVar.P1 k)) ∧
      (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) x0 ≫ act
        = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ x0) ∧
      (IsDominant j.left) ∧
      (MonoidalCategoryStruct.tensorHom j (𝟙 (Work.AbVar.Gm k)) ≫ act = MonObj.mul ≫ j) := by
  haveI : IsDominant (Work.AbVar.P1Action.gmToP1 k).left :=
    Work.AbVar.P1Action.gmToP1_dominant k
  haveI : AlgebraicGeometry.IsIntegral (Work.AbVar.P1 k).left :=
    Work.AbVar.ProjectiveLine.isIntegral_P1 k
  haveI : AlgebraicGeometry.IsProper (Work.AbVar.P1 k).hom :=
    Work.AbVar.ProjectiveLine.isProper_P1 k
  refine ⟨Work.AbVar.P1Action.scalingAct k, Work.AbVar.P1Action.pointInf k,
    Work.AbVar.P1Action.gmToP1 k, ?_, scalingActionData_fixed k, ?_, ?_⟩
  · -- the unit section acts as the identity, using equivariance and the density of the orbit
    refine Work.AbVar.eq_of_isDominant (A := Work.AbVar.P1 k) (J := Work.AbVar.P1 k)
      (Work.AbVar.P1Action.gmToP1 k) ?_
    calc Work.AbVar.P1Action.gmToP1 k ≫ (Work.AbVar.sectionLeft (Work.AbVar.P1 k)
            (Work.AbVar.Gm k) (MonObj.one (X := Work.AbVar.Gm k))
          ≫ Work.AbVar.P1Action.scalingAct k)
        = (Work.AbVar.sectionLeft (Work.AbVar.Gm k) (Work.AbVar.Gm k)
              (MonObj.one (X := Work.AbVar.Gm k))
            ≫ MonoidalCategoryStruct.tensorHom (Work.AbVar.P1Action.gmToP1 k)
                (𝟙 (Work.AbVar.Gm k)))
            ≫ Work.AbVar.P1Action.scalingAct k := by
          rw [← Category.assoc, Work.AbVar.P1Action.gmToP1_sectionLeft k]
      _ = Work.AbVar.sectionLeft (Work.AbVar.Gm k) (Work.AbVar.Gm k)
              (MonObj.one (X := Work.AbVar.Gm k))
            ≫ (MonoidalCategoryStruct.tensorHom (Work.AbVar.P1Action.gmToP1 k)
                (𝟙 (Work.AbVar.Gm k)) ≫ Work.AbVar.P1Action.scalingAct k) := by
          rw [Category.assoc]
      _ = Work.AbVar.sectionLeft (Work.AbVar.Gm k) (Work.AbVar.Gm k)
              (MonObj.one (X := Work.AbVar.Gm k))
            ≫ (MonObj.mul ≫ Work.AbVar.P1Action.gmToP1 k) := by
          rw [scalingActionData_equivariance k]
      _ = (Work.AbVar.sectionLeft (Work.AbVar.Gm k) (Work.AbVar.Gm k)
              (MonObj.one (X := Work.AbVar.Gm k))
            ≫ MonObj.mul) ≫ Work.AbVar.P1Action.gmToP1 k := by
          rw [Category.assoc]
      _ = 𝟙 (Work.AbVar.Gm k) ≫ Work.AbVar.P1Action.gmToP1 k := by
          have h : Work.AbVar.sectionLeft (Work.AbVar.Gm k) (Work.AbVar.Gm k)
              (MonObj.one (X := Work.AbVar.Gm k)) ≫ MonObj.mul = 𝟙 (Work.AbVar.Gm k) :=
            MonObj.lift_comp_one_right (𝟙 (Work.AbVar.Gm k))
              (SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k))
          rw [h]
      _ = Work.AbVar.P1Action.gmToP1 k := by
          rw [Category.id_comp]
      _ = Work.AbVar.P1Action.gmToP1 k ≫ 𝟙 (Work.AbVar.P1 k) := by
          rw [Category.comp_id]
  · exact Work.AbVar.P1Action.gmToP1_dominant k
  · exact scalingActionData_equivariance k

end Work.AbVar.ProjectiveLine
