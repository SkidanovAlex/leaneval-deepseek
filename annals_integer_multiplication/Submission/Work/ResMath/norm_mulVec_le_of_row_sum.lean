import Mathlib

set_option linter.style.haveILetI false

namespace Work.ResMath

/-- If every row sum `∑ j, ‖M i j‖` of a complex matrix `M` is bounded by `R`, then
`‖M u‖ ≤ R * ‖u‖` for the sup norms on the function spaces `n → ℂ` and `m → ℂ`. -/
theorem norm_mulVec_le_of_row_sum {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ i, ∑ j, ‖M i j‖ ≤ R) (u : n → ℂ) :
    ‖M.mulVec u‖ ≤ R * ‖u‖ := by
  rcases isEmpty_or_nonempty m with hm | hm
  · have h0 : M.mulVec u = 0 := funext fun i => (hm.false i).elim
    rw [h0, norm_zero]
    exact mul_nonneg hR (norm_nonneg u)
  · haveI := hm
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    calc ‖(M.mulVec u) i‖ = ‖∑ j, M i j * u j‖ := by
            simp [Matrix.mulVec_apply, dotProduct]
      _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
      _ = ∑ j, ‖M i j‖ * ‖u j‖ := by simp
      _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _)
      _ = (∑ j, ‖M i j‖) * ‖u‖ := by rw [Finset.sum_mul]
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (h i) (norm_nonneg u)

end Work.ResMath
