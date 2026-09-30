import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_isEffective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
/-- **Base change of divisors is monotone.**  If `D ≤ E` as divisors on `C`, then their
pullbacks along a base-change square satisfy `S.divMap D ≤ S.divMap E` on `C'`: indeed
`S.divMap` is additive, so `S.divMap E - S.divMap D = S.divMap (E - D)`, which is effective
because `E - D` is. -/
theorem divMap_mono {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') {D E : Curve.Div C}
    (h : Curve.Div.le D E) : Curve.Div.le (S.divMap D) (S.divMap E) := by
  have h' : Curve.Div.IsEffective (S.divMap (E - D)) := divMap_isEffective S h
  rwa [map_sub] at h'

end Work.CurveBasics.Curve.BCSquare
