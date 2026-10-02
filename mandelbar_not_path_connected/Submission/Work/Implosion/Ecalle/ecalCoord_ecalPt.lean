import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Ecalle

/-- `ecalPt` is a right inverse of `ecalCoord` on the fundamental strip
`-π < Im(2au) ≤ π`, where the principal branch of the logarithm inverts
`exp`.  Indeed `m_a(ζ(u)) = e^{2au}`, so `u(ζ(u)) = log(e^{2au})/(2a) = u`. -/
theorem ecalCoord_ecalPt (a u : ℂ) (ha : a ≠ 0) (hs : ecalE a u ≠ 1)
    (h1 : -(Real.pi) < (2 * a * u).im) (h2 : (2 * a * u).im ≤ Real.pi) :
    ecalCoord a (ecalPt a u) = u := by
  have hm : mobius a (ecalPt a u) = ecalE a u := mobius_ecalPt a u ha hs
  have hlog : Complex.log (mobius a (ecalPt a u)) = 2 * a * u := by
    rw [hm, ecalE]
    exact Complex.log_exp h1 h2
  have h2a : (2 : ℂ) * a ≠ 0 := by simp [ha]
  rw [ecalCoord, hlog]
  rw [show (2 : ℂ) * a * u = (2 * a) * u by ring, mul_div_cancel_left₀ u h2a]

end Work.Implosion.Ecalle
