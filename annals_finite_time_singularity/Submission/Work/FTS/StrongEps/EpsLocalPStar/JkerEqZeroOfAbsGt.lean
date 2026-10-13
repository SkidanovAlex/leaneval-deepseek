import Mathlib.Analysis.Normed.Ring.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

/-- **The kernel vanishes outside the square of side `2ε`.**  If one of the two coordinates of `p`
exceeds `ε` in absolute value, then `p` lies outside the closed ball of radius `ε`, so the rescaled
kernel `Jker ρ ε` vanishes at `p` (`Jker_eq_zero_of_not_mem`, which only needs the mollifier part
`IsMollKernel ρ` of the hypothesis). -/
theorem JkerEqZeroOfAbsGt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : ε < |p.1| ∨ ε < |p.2|) :
    Work.FTS.StrongEps.Jker ρ ε p = 0 := by
  refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ.moll hε ?_
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, not_le]
  rcases hp with hp | hp
  · exact lt_of_lt_of_le hp (le_max_left _ _)
  · exact lt_of_lt_of_le hp (le_max_right _ _)

end Work.FTS.StrongEps.EpsLocalPStar
