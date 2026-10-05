import Mathlib
import Submission.Work.RPCore.Saddle.SplitSpectralDiag

namespace Work.RPCore.Saddle

theorem diag_inner_le {n : ℕ} (d : Fin n → ℝ) {c : ℝ} (h : ∀ i, d i ≤ -c)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (diagCLM d x) x ≤ -c * ‖x‖ ^ 2 := by
  have hsum : inner ℝ (diagCLM d x) x = ∑ i, d i * (x i) ^ 2 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.inner_apply, diagCLM_apply]
    ring
  rw [hsum, EuclideanSpace.real_norm_sq_eq]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

end Work.RPCore.Saddle
