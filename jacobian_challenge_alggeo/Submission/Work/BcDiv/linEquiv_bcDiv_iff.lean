import Mathlib
import Submission.Work.BcDiv.Basic
import Submission.Work.CurveBasics.Curve.BCSquare.linEquiv_divMap_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

universe u

/-- **B2, linear equivalence.** Two divisors on `(C_L)_F` are linearly equivalent if and only if
their images under the identification `Work.BcDiv.bcDiv` are linearly equivalent on `C_F`.

Proof route: `Curve.BCSquare.linEquiv_divMap_iff`
(`Submission/Work/CurveBasics/Curve/BCSquare/linEquiv_divMap_iff.lean`) applied to the comparison
square `Work.BcDiv.bcSq`, in the symmetric form (the cited result yields
`LinEquiv C (bcDiv D) (bcDiv D') ↔ LinEquiv (C.baseChange L) D D'`), together with
`Work.BcDiv.bcDiv_apply`. -/
theorem linEquiv_bcDiv_iff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u}
    [Field L] [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] (D D' : Work.GCBasics.Dv (C.baseChange L) F) :
    Work.GCBasics.LinEquiv (C.baseChange L) D D' ↔
      Work.GCBasics.LinEquiv C (Work.BcDiv.bcDiv D) (Work.BcDiv.bcDiv D') := by
  rw [Work.GCBasics.linEquiv_def, Work.GCBasics.linEquiv_def,
    Work.BcDiv.bcDiv_apply, Work.BcDiv.bcDiv_apply]
  exact Iff.symm (Work.CurveBasics.Curve.BCSquare.linEquiv_divMap_iff
    (Work.BcDiv.bcSq (C := C) (L := L) (F := F)) D D')

end Work.BcDiv
