import Mathlib

namespace Work.Whitney.BumpModel

open scoped ContDiff

/-- There is a smooth cut-off function `χ : ℝⁿ → ℝ` (with the **sup** norm on `Fin n → ℝ`) which is
`1` on the ball of radius `2`, strictly positive on the open ball of radius `4`, and vanishes on the
complement of the closed ball of radius `4`. -/
theorem exists_bump_chi (n : ℕ) [NeZero n] :
    ∃ χ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 2 → χ x = 1) ∧ (∀ x, ‖x‖ < 4 → χ x ≠ 0) ∧ (∀ x, 4 ≤ ‖x‖ → χ x = 0) := by
  let f : ContDiffBump (0 : Fin n → ℝ) := ContDiffBump.mk 2 4 (by norm_num) (by norm_num)
  refine ⟨f, f.contDiff, fun x => f.nonneg, fun x => f.le_one, ?_, ?_, ?_⟩
  · intro x hx
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx
  · intro x hx
    exact ne_of_gt (f.pos_of_mem_ball (by rw [Metric.mem_ball, dist_zero_right]; exact hx))
  · intro x hx
    exact f.zero_of_le_dist (by rw [dist_zero_right]; exact hx)

end Work.Whitney.BumpModel
