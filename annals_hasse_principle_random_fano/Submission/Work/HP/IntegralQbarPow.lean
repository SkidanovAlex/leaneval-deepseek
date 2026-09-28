import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.QbarCoords
import Submission.Work.HP.QbarIntegrable
import Submission.Work.HP.QbarInnerIntegral
import Submission.Work.HP.QbarOuterIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Work.HP

theorem IntegralQbarPow (d : ℕ) : ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then (Real.sqrt (qbar u)) ^ d else 0) = 8 / ((d:ℝ) + 2) := by
  rw [qbar_integral_eq_prod d]
  change (∫ p : ℝ × ℝ, qbCo d p ∂(volume.prod volume)) = 8 / ((d:ℝ) + 2)
  rw [integral_prod (qbCo d) (qbarCo_integrable d)]
  have hinner : ∀ x : ℝ, (∫ y : ℝ, qbCo d (x, y))
      = (if |x| ≤ 1 then 2 * ((d:ℝ) * |x| ^ (d + 1) + 1) / ((d:ℝ) + 1) else 0) := by
    intro x
    simpa [qbCo] using QbarInnerIntegral d x
  rw [show (∫ x : ℝ, ∫ y : ℝ, qbCo d (x, y))
        = ∫ x : ℝ, (if |x| ≤ 1 then 2 * ((d:ℝ) * |x| ^ (d + 1) + 1) / ((d:ℝ) + 1) else 0)
      from by
        apply integral_congr_ae
        filter_upwards with x
        exact hinner x]
  exact QbarOuterIntegral d

end Work.HP
