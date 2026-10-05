import Mathlib
import Submission.Work.RPCore.Saddle.SplitSpectralDiag

namespace Work.RPCore.Saddle

theorem diag_le_inner {n : ℕ} (d : Fin n → ℝ) {c : ℝ} (h : ∀ i, c ≤ d i)
    (x : EuclideanSpace ℝ (Fin n)) :
    c * ‖x‖ ^ 2 ≤ inner ℝ (diagCLM d x) x := by
  -- Both sides are computed coordinatewise: the inner product against `x` is
  -- `∑ i, d i * (x i)^2`, while `‖x‖^2 = ∑ i, (x i)^2`.
  have key : inner ℝ (diagCLM d x) x = ∑ i : Fin n, d i * (x i) ^ 2 := by
    rw [PiLp.inner_apply]
    simp [mul_left_comm, sq]
  have hnorm : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq x]
    rw [PiLp.inner_apply]
    simp [sq]
  rw [key, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum
    (fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg (x i)))

end Work.RPCore.Saddle
