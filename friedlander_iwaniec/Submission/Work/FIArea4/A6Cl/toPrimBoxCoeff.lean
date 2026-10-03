import Mathlib
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.prim_of_beta6

namespace Work.FIArea4.A6Cl

/-- **A round-6 coefficient is a primitive box coefficient.**

`Work.FITop4.IsBetaCoeff6` strengthens the round-4 predicate `Work.FITop4.IsBetaCoeff` by the
(5.7) restriction to one class modulo eight and by the axis-free region of §5, and
`Work.FITop4.IsBetaCoeff6.exists_toBetaCoeff` exhibits the underlying round-4 array `β'`, of which
`β` is the restriction

  `β z = if SameClass8 z z0 ∧ IsAxisFree Pa z then β' z else 0`.

Both components of `Work.FIArea4.IsPrimBoxCoeff` transfer from `β'`:

* the box predicate `Work.FITop3.IsBoxCoeff` — the pointwise norm bound `‖β z‖ ≤ τ(|z|²)` and the
  support condition `β z ≠ 0 → InPolarBox Pa φ z ∧ NoSmallPrimes Pa z` — follows from that of `β'`
  by `Work.FITop4.IsBetaCoeff.toBoxCoeff`, since restricting the support only shrinks it;
* primitivity `(Re z, 2 Im z) = 1` (FI (11.6)) is `Work.FIArea4.IsBetaCoeff4.primitive` applied to
  `β'`: the polar box (5.14) makes `z` primary, so `Re z` is odd, and the Möbius factor of (5.13)
  makes `|z|²` squarefree, so `(Re z, Im z) = 1`; together `(Re z, 2 Im z) = 1`.

This is exactly the statement of `Work.FIArea4.prim_of_beta6`, restated in the namespace of the
§6 coefficient chain (`A6Close` consumes it as `A6Cl.toPrimBoxCoeff`). -/
theorem toPrimBoxCoeff {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    Work.FIArea4.IsPrimBoxCoeff Pa φ β :=
  Work.FIArea4.prim_of_beta6 h

end Work.FIArea4.A6Cl
