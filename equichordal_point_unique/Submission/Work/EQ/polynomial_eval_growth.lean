import Mathlib

namespace Work.EQ

theorem polynomial_eval_growth (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖p.eval z‖ ≤ C * ‖z‖ ^ p.natDegree := by
  refine ⟨max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro z hz
  have heval : p.eval z = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i :=
    Polynomial.eval_eq_sum_range z
  rw [heval]
  calc ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖z‖ ^ i := by
          simp [norm_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖z‖ ^ p.natDegree := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_le : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hi_le) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
          rw [Finset.sum_mul]
    _ ≤ max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Work.EQ
