import Mathlib
import Submission.Work.SeedCertNum.Jet2
import Submission.Work.Landing.Family.deriv_tsq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

/-- The second derivative of the holomorphic second iterate
`Tsq c = fun z => (z^2 + star c)^2 + c` is `12 z^2 + 4 star c` everywhere.
This is the analytic input to item A3 of the `SeedCertNum` contract (the certified
parabolic point of `(Tsq c)^[5]` is simple). -/
theorem deriv2_Tsq (c u : ℂ) :
    deriv (deriv (Work.Landing.Tsq c)) u = 12 * u ^ 2 + 4 * star c := by
  have h1 : deriv (Work.Landing.Tsq c) = fun z => 4 * z * (z ^ 2 + star c) := by
    funext z
    exact Work.Landing.Family.deriv_tsq c z
  rw [h1]
  have hz : HasDerivAt (fun z : ℂ => z ^ 2 + star c) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (star c)
  have h4 : HasDerivAt (fun z : ℂ => 4 * z) 4 u := by
    simpa using (hasDerivAt_id u).const_mul (4 : ℂ)
  have hprod : HasDerivAt (fun z : ℂ => 4 * z * (z ^ 2 + star c))
      (4 * (u ^ 2 + star c) + 4 * u * (2 * u)) u :=
    h4.mul hz
  rw [hprod.deriv]
  ring

end Work.SeedCertNum
