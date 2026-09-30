import Mathlib
import Submission.Work.BcDiv.Basic
import Submission.Work.RiemannRoch.ExportCB

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

universe u

/-- **B2, degree.** The identification `Work.BcDiv.bcDiv` of the divisor groups of `(C_L)_F` and
`C_F` (fields `K → L → F`, `C` a curve over `K`) preserves the degree.

Proof route: `Work.BcDiv.bcDiv_apply` (`bcDiv D = (Work.BcDiv.bcSq).divMap D`, an `rfl`-lemma)
followed by `Work.RiemannRoch.Curve.deg_divMap` (`Submission/Work/RiemannRoch/ExportCB.lean`)
applied to the comparison square
`Work.BcDiv.bcSq : Curve.BCSquare ((C.baseChange L).baseChange F) (C.baseChange F)`.
Suggested proof: `rw [Work.BcDiv.bcDiv_apply]; exact Work.RiemannRoch.Curve.deg_divMap _ D`. -/
theorem deg_bcDiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : Work.GCBasics.Dv (C.baseChange L) F) :
    Work.GCBasics.Ddeg C F (Work.BcDiv.bcDiv D) = Work.GCBasics.Ddeg (C.baseChange L) F D := by
  rw [Work.BcDiv.bcDiv_apply]
  exact Work.RiemannRoch.Curve.deg_divMap _ D

end Work.BcDiv
