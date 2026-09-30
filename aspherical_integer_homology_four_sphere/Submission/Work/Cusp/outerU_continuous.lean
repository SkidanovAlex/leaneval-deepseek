import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `outerU v x = ⟪x, κ_{v,1}⟫ / ‖κ_{v,1}‖²` is the inner product of `x` with the fixed lattice
vector `κ_{v,1}`, divided by the constant `‖κ_{v,1}‖²`; hence it is continuous in `x`. -/
theorem outerU_continuous (v : Fin 5) : Continuous (outerU v) := by
  unfold outerU kappaCoord
  exact (continuous_id.inner continuous_const).div_const _

end Work.Cusp
