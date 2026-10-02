/-
# TripodCert — the radius check of the uniqueness disc

Area `Submission/Work/TripodCert/`.  The containment test `inUBall` of `Num.lean` checks the
rational inequality `(cx - zx)² + (cy - zy)² ≤ (R - r)²`; the geometric containment
`disk ⊆ closedBall z₀ R` needs in addition `r ≤ R`.  This module supplies that (trivial) integer
check, kept out of `Num.lean` so that the large emitted `decide` module `Check.lean` is not
invalidated by it.
-/
import Mathlib
import Submission.Work.TripodCert.Num

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

/-- The radius check of one angle class of a data list: every sub-disk radius is `≤ R`. -/
def radLeT (R : Int) (l : List Int) (j : Nat) : Bool :=
  allS angQsT (fun i => decide (gI l (3 * ((j % 6) * NC + i) + 2) ≤ R))

/-- **The radius of the uniqueness disc**, in mantissas: it contains the periodic boxes of the
angle classes `0` and `2` (`chkUBallU_0`, `chkUBallU_2`) and is small enough for the derivative
certificate of `UniqueDefs.lean`. -/
def URmU : Int := 54608039

end Work.TripodCert
