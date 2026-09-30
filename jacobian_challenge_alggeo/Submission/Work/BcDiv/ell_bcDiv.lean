import Mathlib
import Submission.Work.BcDiv.Basic
import Submission.Work.CurveBasics.Curve.BCSquare.l_divMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

universe u

/-- **B2, ℓ.** The dimension `ℓ` of the Riemann-Roch space is invariant under the identification
`Work.BcDiv.bcDiv` of the divisor groups of `(C_L)_F` and `C_F`.

Proof route: `Work.BcDiv.bcDiv_apply` and `Curve.BCSquare.l_divMap`
(`Submission/Work/CurveBasics/Curve/BCSquare/l_divMap.lean`) applied to `Work.BcDiv.bcSq`; the
statements match up to `rfl` since `ell C D = (C.baseChange F).l D`.
Suggested proof: `rw [Work.BcDiv.bcDiv_apply]; exact (Work.CurveBasics.Curve.BCSquare.l_divMap _ D).symm`. -/
theorem ell_bcDiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : Work.GCBasics.Dv (C.baseChange L) F) :
    Work.GCBasics.ell (C.baseChange L) D = Work.GCBasics.ell C (Work.BcDiv.bcDiv D) := by
  rw [Work.BcDiv.bcDiv_apply]
  exact (Work.CurveBasics.Curve.BCSquare.l_divMap _ D).symm

end Work.BcDiv
