import Mathlib
import Submission.Work.RPCore.Saddle.SplitSpectralDiag

namespace Work.RPCore.Saddle

theorem diag_norm_bound {n : ℕ} (d : Fin n → ℝ) {K : ℝ} (hK : 0 ≤ K) (h : ∀ i, |d i| ≤ K)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖diagCLM d x‖ ≤ K * ‖x‖ := by
  have h1 : ‖diagCLM d x‖ ^ 2 = ∑ i, (d i * x i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have h2 : ∑ i, (d i * x i) ^ 2 ≤ ∑ i, (K * x i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hx : (0 : ℝ) ≤ (x i) ^ 2 := sq_nonneg _
    have hd : (d i) ^ 2 ≤ K ^ 2 := by
      apply sq_le_sq'
      · exact (abs_le.mp (h i)).1
      · exact (abs_le.mp (h i)).2
    calc (d i * x i) ^ 2 = (d i) ^ 2 * (x i) ^ 2 := by ring
      _ ≤ K ^ 2 * (x i) ^ 2 := mul_le_mul_of_nonneg_right hd hx
      _ = (K * x i) ^ 2 := by ring
  have h3 : ∑ i, (K * x i) ^ 2 = K ^ 2 * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h4 : ‖diagCLM d x‖ ^ 2 ≤ (K * ‖x‖) ^ 2 := by
    rw [h1]
    calc ∑ i, (d i * x i) ^ 2 ≤ ∑ i, (K * x i) ^ 2 := h2
      _ = K ^ 2 * ‖x‖ ^ 2 := h3
      _ = (K * ‖x‖) ^ 2 := by ring
  have h5 : (0 : ℝ) ≤ ‖diagCLM d x‖ := norm_nonneg _
  have h6 : (0 : ℝ) ≤ K * ‖x‖ := mul_nonneg hK (norm_nonneg _)
  have := sq_le_sq.mp h4
  rwa [abs_of_nonneg h5, abs_of_nonneg h6] at this

end Work.RPCore.Saddle
