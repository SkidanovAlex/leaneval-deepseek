import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory
open scoped ENNReal

namespace Work.MRMT.Found

/-- If a disk in `ℂ` has radius `R ≥ 0`, the square root of its (planar Lebesgue)
area equals `√(π R²)`.  The volume of a closed disk is `π R²`, so this is immediate
from `Complex.volume_closedBall` once the `ENNReal` value is converted to a real. -/
theorem sqrt_volume_closedBall (R : ℝ) (hR : 0 ≤ R) :
    Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) R)).toReal) =
      Real.sqrt (Real.pi * R ^ 2) := by
  have hvol : (MeasureTheory.volume (Metric.closedBall (0 : ℂ) R))
      = ENNReal.ofReal (Real.pi * R ^ 2) := by
    rw [Complex.volume_closedBall]
    rw [show (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi from by
      rw [← NNReal.coe_real_pi]; exact ENNReal.ofReal_coe_nnreal.symm]
    rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (pow_nonneg hR 2)]
    ring_nf
  rw [hvol, ENNReal.toReal_ofReal (by positivity)]

end Work.MRMT.Found
