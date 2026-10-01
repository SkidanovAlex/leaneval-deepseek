import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

namespace Work.LinnikAreas.Density4

theorem thetaDiag_tdH_nonneg (σ A : ℝ) : ∀ n : ℕ, 0 ≤ tdH σ A n := by
  intro n
  unfold tdH
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.exp_pos _).le

end Work.LinnikAreas.Density4
