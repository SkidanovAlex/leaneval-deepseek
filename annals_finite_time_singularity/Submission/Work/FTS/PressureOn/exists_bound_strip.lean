import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

theorem exists_bound_strip {g : R3 → ℝ → R3}
    (hg : Continuous fun p : R3 × ℝ => g p.1 p.2) (R t : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ Metric.closedBall (0 : R3) R,
      ∀ s ∈ Set.Icc (t - 1 / 2) (t + 1 / 2), ‖g y s‖ ≤ M := by
  have hcomp : IsCompact (Metric.closedBall (0 : R3) R ×ˢ Set.Icc (t - 1 / 2) (t + 1 / 2)) :=
    (isCompact_closedBall (0 : R3) R).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hy s hs
  exact le_trans (hC (y, s) ⟨hy, hs⟩) (le_max_left _ _)

end Work.FTS.PressureOn
