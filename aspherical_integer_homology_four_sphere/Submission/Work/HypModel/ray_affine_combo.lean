import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The null-ray map `y ↦ (y,1)` is affine: it is the linear embedding `y ↦ (y,0)` followed by the
constant translation by `e₄`, and its last coordinate is constantly `1`.  Consequently it
interpolates affine combinations. -/
theorem ray_affine_combo (t : ℝ) (y z : E4) :
    ray ((1 - t) • y + t • z) = (1 - t) • ray y + t • ray z := by
  ext i
  fin_cases i <;> simp [ray]

end Work.HypModel
