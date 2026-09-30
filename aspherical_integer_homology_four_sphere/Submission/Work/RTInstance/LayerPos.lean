/-
# Positivity of the models of a chart layer

The structure `Work.Space.ModelAtlas` requires each model to be positive definite on *all* of `E4`
(the positivity is consumed by `ModelAtlas.gM` only at the chart images, but it is a field of the
structure).  This file proves it for the three layers of `Work.RTInstance.ChartLayer`:

* the upper half space layer `uhs δ` needs only `0 < δ` (`Work.RTInstance.uhsModel_pos`),
* the warped layer of a profile is positive because `posExt P.f (1/8)` and `P.h` are positive
  everywhere (`Work.RTInstance.warpedModelA_pos`, `Work.RTInstance.fillProfile_posExt_pos`),
* the flat layer needs `h₀ ≠ 0` (`Work.RTInstance.flatModel_pos`).

The positivity input of a layer that does not depend on the point is `ChartLayer.okAnywhere`;
`ChartLayer_model_pos_of` turns it into the `model_pos` field.
-/
import Mathlib
import Submission.Work.RTInstance.Models
import Submission.Work.RTInstance.posExt_pos
import Submission.Work.RTInstance.uhsModel_pos
import Submission.Work.RTInstance.warpedModelA_pos
import Submission.Work.RTInstance.flatModel_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace
open Bundle

namespace Work.RTInstance

/-- **The positive modification of a filling profile is positive** (the profile is positive on
`(0, ∞)` and nonnegative on `[0, ∞)`, and `1/8 < 1/2`). -/
theorem fillProfile_posExt_pos (P : Work.Profiles.FillProfile) :
    ∀ r, 0 < posExt P.f (1/8) r := by
  have hc : (0:ℝ) < 1/8 := by norm_num
  refine posExt_pos P.f (1/8) hc ?_ ?_
  · intro r hr
    exact P.f_pos r (lt_of_lt_of_le (by norm_num) hr)
  · intro r hr0 _hrc
    have h := P.f_monotone hr0
    rwa [P.f_core 0 (by norm_num)] at h

/-- **The positivity of the model of a layer from its global non-degeneracy input.** -/
theorem ChartLayer_model_pos_of (l : ChartLayer) (hl : l.okAnywhere) (q v : E4) (hv : v ≠ 0) :
    0 < l.model q v v := by
  cases l with
  | uhs δ => exact uhsModel_pos δ hl q v hv
  | warped P => exact warpedModelA_pos (fillProfile_posExt_pos P) P.h_pos q v hv
  | flat h₀ => exact flatModel_pos h₀ hl q v hv

end Work.RTInstance
