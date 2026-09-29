import Mathlib
import Submission.Work.CLift.bridge

namespace Work.CLift

open Submission.CDTPlan
open Metric

/-- Schwarz lemma for the Theorem C contour map: `psiC` is holomorphic on the unit disc with
`psiC 0 = 0` and `‖psiC z‖ ≤ 3/4` on the closed unit disc, hence `‖psiC z‖ ≤ (3/4)‖z‖`. -/
theorem psiC_schwarz (hP : PsiCFacts) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖psiC z‖ ≤ 3 / 4 * ‖z‖ := by
  intro z hz
  rcases lt_or_eq_of_le hz with hlt | heq
  · have hd : DifferentiableOn ℂ psiC (ball 0 1) := hP.2.1
    have hmaps : Set.MapsTo psiC (ball 0 1) (closedBall (psiC 0) (3 / 4)) := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      rw [mem_closedBall_iff_norm, hP.2.2.1, sub_zero]
      exact hP.2.2.2.2.1 w (mem_closedBall_zero_iff.mpr (le_of_lt hw))
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps (mem_ball_zero_iff.mpr hlt)
    rw [hP.2.2.1] at h
    rwa [dist_eq_norm, sub_zero, dist_eq_norm, sub_zero, div_one] at h
  · rw [heq, mul_one]
    exact hP.2.2.2.2.1 z (by rw [mem_closedBall_zero_iff, heq])

end Work.CLift
