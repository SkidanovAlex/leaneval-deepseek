import Mathlib
import Submission.Work.Diff.GE.react.rmReact_contDiff
import Submission.Work.Diff.GE.react.rmReact_fderiv_bound
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.Diff.GE.EvolA

open Submission.Diff.Alg

variable {n : ℕ}

/-- The reaction map `rmReact` is quadratic, so it vanishes at the origin. -/
theorem rmReact_zero (n : ℕ) : Work.Diff.GE.rmReact n (0 : Curv4 n) = 0 := by
  funext i j k l
  simp only [Work.Diff.GE.rmReact_apply, Pi.sub_apply, Pi.zero_apply]
  simp only [Submission.Diff.Alg.Q, Work.Diff.Evol.Xact, Work.Diff.Evol.ricArr]
  simp

/-- The reaction map `rmReact = Q − Xact` is bounded by a constant times `‖R‖²`. -/
theorem rmReact_norm_le (n : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ R : Curv4 n, ‖Work.Diff.GE.rmReact n R‖ ≤ CF * ‖R‖ * ‖R‖ := by
  obtain ⟨CF', hCF'0, hb⟩ := Work.Diff.GE.react.rmReact_fderiv_bound n
  refine ⟨max CF' 0, le_max_right _ _, fun R => ?_⟩
  have hdiff : ∀ x ∈ Metric.closedBall (0 : Curv4 n) ‖R‖,
      DifferentiableAt ℝ (Work.Diff.GE.rmReact n) x :=
    fun x _ => (Work.Diff.GE.react.rmReact_contDiff n).differentiable (by simp) x
  have hbound : ∀ x ∈ Metric.closedBall (0 : Curv4 n) ‖R‖,
      ‖fderiv ℝ (Work.Diff.GE.rmReact n) x‖ ≤ max CF' 0 * ‖R‖ := by
    intro x hx
    have hx' : ‖x‖ ≤ ‖R‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    calc ‖fderiv ℝ (Work.Diff.GE.rmReact n) x‖ ≤ CF' * ‖x‖ := hb x
      _ ≤ CF' * ‖R‖ := mul_le_mul_of_nonneg_left hx' hCF'0
      _ ≤ max CF' 0 * ‖R‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hmem0 : (0 : Curv4 n) ∈ Metric.closedBall (0 : Curv4 n) ‖R‖ := by
    simp [Metric.mem_closedBall]
  have hmemR : R ∈ Metric.closedBall (0 : Curv4 n) ‖R‖ := by
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall (0 : Curv4 n) ‖R‖) hmem0 hmemR
  rw [rmReact_zero n, sub_zero, sub_zero] at hmvt
  calc ‖Work.Diff.GE.rmReact n R‖ ≤ (max CF' 0 * ‖R‖) * ‖R‖ := hmvt
    _ = max CF' 0 * ‖R‖ * ‖R‖ := by ring

/-- The reaction map of the fixed-vector curvature evolution is bounded by a constant times
`‖R‖²`. -/
theorem reactionMap_norm_le (n : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ R : Curv4 n, ‖Work.Diff.GE.reactionMap R‖ ≤ CF * ‖R‖ * ‖R‖ := by
  obtain ⟨CF, h0, hb⟩ := rmReact_norm_le n
  exact ⟨CF, h0, fun R => by rw [reactionMap_eq_rmReact R]; exact hb R⟩

end Work.Diff.GE.EvolA
