import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

namespace Work.A7.ModelApproxCore_aux

/-- The product of two convolution operators is the double sum of the products of the
corresponding summands. -/
theorem convOp_mul_tsum {κ κ' u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hκ : Summable fun j : ℤ => ‖κ j‖) (hκ' : Summable fun j : ℤ => ‖κ' j‖)
    (hu : ∀ y, ‖u y‖ ≤ Cu) (hv : ∀ y, ‖v y‖ ≤ Cv) (a b : ℤ) :
    Work.KMTAreas.A7.convOp κ u a * Work.KMTAreas.A7.convOp κ' v b
      = ∑' z : ℤ × ℤ, (κ z.1 * u (a - z.1)) * (κ' z.2 * v (b - z.2)) := by
  have hf' : Summable fun j : ℤ => κ j * u (a - j) :=
    Summable.of_norm_bounded (hκ.mul_right Cu) fun j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hu (a - j)) (norm_nonneg _)
  have hg' : Summable fun j : ℤ => κ' j * v (b - j) :=
    Summable.of_norm_bounded (hκ'.mul_right Cv) fun j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hv (b - j)) (norm_nonneg _)
  rw [Work.KMTAreas.A7.convOp, Work.KMTAreas.A7.convOp]
  exact tsum_mul_tsum_of_summable_norm hf'.norm hg'.norm

end Work.A7.ModelApproxCore_aux
