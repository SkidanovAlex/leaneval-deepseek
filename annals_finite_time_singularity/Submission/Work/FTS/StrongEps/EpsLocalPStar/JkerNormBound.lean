import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem JkerNormBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × ℝ, ‖Work.FTS.StrongEps.Jker ρ ε p‖ ≤ M := by
  -- `Jker ρ ε` is continuous (as a rescaling of the `C^∞` kernel `ρ`) and compactly supported
  -- (the support of `ρ` is contained in the unit ball, so `Jker ρ ε` is supported in the ball
  -- of radius `ε`); a continuous compactly supported function on `ℝ × ℝ` is bounded in norm.
  obtain ⟨C, hC⟩ :=
    (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).bounded_above_of_compact_support
      (Work.FTS.StrongEps.Jker_hasCompactSupport hρ.moll hε)
  exact ⟨max C 0, le_max_right C 0, fun p => le_trans (hC p) (le_max_left C 0)⟩

end Work.FTS.StrongEps.EpsLocalPStar
