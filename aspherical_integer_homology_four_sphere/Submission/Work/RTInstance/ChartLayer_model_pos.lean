import Mathlib
import Submission.Work.RTInstance.Models
import Submission.Work.RTInstance.uhsModel_pos
import Submission.Work.RTInstance.warpedModelA_pos
import Submission.Work.RTInstance.flatModel_pos
import Submission.Work.RTInstance.posExt_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTInstance

/-- The modified warping function `posExt P.f (1/8)` of a filling profile is positive everywhere:
it is positive on `[1/8, ∞)` because `P.f > 0` on `(0, ∞)`, and on `(-∞, 1/8)` by
`posExt_pos` together with the nonnegativity of `P.f` on `[0, ∞)` (which follows from `P.f 0 = 0`
and the monotonicity of `P.f`). -/
theorem posExt_fillProfile_pos (P : Work.Profiles.FillProfile) (r : ℝ) :
    0 < posExt P.f (1/8) r :=
  posExt_pos P.f (1/8) (by norm_num)
    (fun r hr => P.f_pos r (by linarith))
    (fun r hr _ => by
      have h0 : (0 : ℝ) ≤ P.f 0 := by rw [P.f_core 0 (by norm_num)]
      exact le_trans h0 (P.f_monotone hr))
    r

theorem ChartLayer_model_pos (l : ChartLayer) {q : E4} (hq : l.ok q) (v : E4)
    (hv : v ≠ 0) : 0 < l.model q v v := by
  cases l with
  | uhs δ => exact uhsModel_pos δ hq.1 q v hv
  | warped P => exact warpedModelA_pos (posExt_fillProfile_pos P) P.h_pos q v hv
  | flat h₀ => exact flatModel_pos h₀ hq q v hv

end Work.RTInstance
