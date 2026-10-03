import Mathlib
import Submission.Work.Pert.pert2v2.walkY2

namespace Work.Pert.pert2v2

theorem margA_step_le {Ξ : ℝ} {α : ℂ} {z w : ℂ} (h : ‖w - (z - 1)‖ ≤ 1 / 32) :
    Work.Pert.margA_g Ξ α z - 17 / 16 ≤ Work.Pert.margA_g Ξ α w := by
  -- `margA_g Ξ α` is `2`-Lipschitz and the shift by `1` costs exactly `1`:
  -- `margA_g Ξ α w ≥ margA_g Ξ α (z - 1) - 2‖w - (z - 1)‖ ≥ (margA_g Ξ α z - 1) - 2/32`.
  have h1 := Work.Pert.margA_sub_le Ξ α w (z - 1)
  have h2 := Work.Pert.pert2v2.margA_g_sub_one (Ξ := Ξ) (α := α) z
  have h3 : 2 * ‖w - (z - 1)‖ ≤ 2 * (1 / 32 : ℝ) := by linarith
  linarith

end Work.Pert.pert2v2
