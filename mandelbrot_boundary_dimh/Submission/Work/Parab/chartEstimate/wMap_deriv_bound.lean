import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_deriv_bound
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

namespace Work.Parab.chartEstimate

theorem wMap_deriv_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') {w : ℂ}
    (hw : max (1 / r + 1) 5 < ‖w‖) :
    ‖deriv (Work.FatouCoord.wMap f) w - 1‖ ≤ 4 * (A' + 4) / ‖w‖ ^ 2 := by
  have h1r : 1 / r < ‖w‖ := by
    have h := lt_of_le_of_lt (le_max_left (1 / r + 1) (5 : ℝ)) hw
    linarith
  have h4 : (4 : ℝ) ≤ ‖w‖ := by
    have h := lt_of_le_of_lt (le_max_right (1 / r + 1) (5 : ℝ)) hw
    linarith
  have h := Work.FatouCoord.Estimate.deriv_wMap_bound_aux hb h1r h4
  simpa [Work.FatouCoord.Estimate.Kderiv] using h

end Work.Parab.chartEstimate
