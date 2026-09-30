import Mathlib
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTInstance

/-- The warped filling model `warpedModelA f h` is positive definite on all of `E4`, provided the
modified warping function `posExt f (1/8)` and the profile `h` are strictly positive everywhere.
This is the model of the polar charts of the atlas (`Work.RTInstance.ChartLayer.model`). -/
theorem warpedModelA_pos {f h : ℝ → ℝ} (hp : ∀ r, 0 < posExt f (1/8) r)
    (hh : ∀ r, 0 < h r) (q : E4) (v : E4) (hv : v ≠ 0) :
    0 < warpedModelA f h q v v := by
  apply diagQuad_pos _ v hv
  intro i
  fin_cases i
  · norm_num
  · exact pow_pos (hp (q 0)) 2
  · exact pow_pos (hh (q 0)) 2
  · exact pow_pos (hh (q 0)) 2

end Work.RTInstance
