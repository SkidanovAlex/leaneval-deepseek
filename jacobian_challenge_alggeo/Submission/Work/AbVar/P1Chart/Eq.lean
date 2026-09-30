import Submission.Work.AbVar.P1Chart.ChartK
import Submission.Work.AbVar.P1Chart.Cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization MvPolynomial

noncomputable section

universe u

namespace Work.AbVar.P1Chart

/-- The identification of `k` with the degree zero part used by `P1BaseEquiv` agrees with
`constToZero`. -/
lemma p1BaseEquiv_toRingHom_eq (k : Type u) [Field k] :
    (Work.AbVar.p1BaseEquiv k).toRingHom = ProjectiveLine.constToZero (R := k) := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  rfl

end Work.AbVar.P1Chart
