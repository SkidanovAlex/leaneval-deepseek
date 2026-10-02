import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

/-- Lipschitz-type estimate for the holomorphic second iterate `Tsq` of the tricorn map:
`Tsq c z - Tsq c w = (z - w)(z + w)(z² + w² + 2 c̄)`, and each factor is bounded by the
corresponding term on the right. -/
theorem norm_Tsq_sub_le (c z w : ℂ) :
    ‖Work.Landing.Tsq c z - Work.Landing.Tsq c w‖
      ≤ ‖z - w‖ * (‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * ‖c‖) := by
  have hid : Work.Landing.Tsq c z - Work.Landing.Tsq c w
      = (z - w) * (z + w) * (z ^ 2 + w ^ 2 + 2 * star c) := by
    unfold Work.Landing.Tsq; ring
  rw [hid]
  rw [norm_mul, norm_mul]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (norm_add_le z w) (norm_nonneg _)
  · have : ‖z ^ 2 + w ^ 2 + 2 * star c‖ ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * ‖c‖ := by
      calc ‖z ^ 2 + w ^ 2 + 2 * star c‖
          ≤ ‖z ^ 2 + w ^ 2‖ + ‖(2 : ℂ) * star c‖ := norm_add_le _ _
        _ ≤ (‖z ^ 2‖ + ‖w ^ 2‖) + ‖(2 : ℂ) * star c‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * ‖c‖ := by
            rw [norm_pow, norm_pow, norm_mul, norm_star]; norm_num
    exact this
  · positivity
  · positivity

end Work.TripodCert
