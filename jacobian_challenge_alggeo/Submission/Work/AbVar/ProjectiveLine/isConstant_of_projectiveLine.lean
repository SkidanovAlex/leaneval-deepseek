import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.P1.const_of_action
import Submission.Work.AbVar.Rigidity.rigidity
import Submission.Work.AbVar.ProjectiveLine.isProper_P1
import Submission.Work.AbVar.ProjectiveLine.geometricallyIntegral_P1
import Submission.Work.AbVar.ProjectiveLine.scalingActionData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Every morphism `ℙ¹ ⟶ A` into a proper group scheme over a field is constant

This is the `P1CONST` item of the contract for the Jacobian challenge.  The proof runs the
rigidity argument of `Work.AbVar.P1.const_of_action` with

* `X = ℙ¹ = Proj k[X₀,X₁]`, proper (`Work.AbVar.ProjectiveLine.isProper_P1`) and geometrically
  integral (`Work.AbVar.ProjectiveLine.geometricallyIntegral_P1`) over `k`,
* the scaling action of `𝔾_m` on `ℙ¹`, together with a fixed point and a dominant orbit map,
  supplied by `Work.AbVar.ProjectiveLine.scalingActionData`.

-/

namespace Work.AbVar.ProjectiveLine

open CategoryTheory in
theorem isConstant_of_projectiveLine {k : Type*} [Field k] {A : Work.AbVar.Sch k}
    [CategoryTheory.GrpObj A] [AlgebraicGeometry.IsProper A.hom] (φ : Work.AbVar.P1 k ⟶ A) :
    ∃ c : Work.AbVar.Point A,
      φ = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) ≫ c := by
  haveI := isProper_P1 k
  haveI := geometricallyIntegral_P1 k
  obtain ⟨act, x0, j, h1, hfix, hdom, horb⟩ := scalingActionData k
  haveI : AlgebraicGeometry.IsDominant j.left := hdom
  exact Work.AbVar.P1.const_of_action act h1 x0 hfix j horb φ

end Work.AbVar.ProjectiveLine
