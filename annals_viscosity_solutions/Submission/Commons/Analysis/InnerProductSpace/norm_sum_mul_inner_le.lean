import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

/-- Weighted estimate for a sum of inner products: if the weights `m i` are nonnegative and the
second family `w` is bounded in norm by `Md`, then the weighted sum of the inner products
`⟪u i, w i⟫` is bounded by `(∑ i, m i) * ‖u‖ * Md`, where `u` carries the `L²` norm of
`EuclideanSpace E (Fin N)`. -/
theorem norm_sum_mul_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (u w : EuclideanSpace E (Fin N))
    {Md : ℝ} (hMd : 0 ≤ Md) (hw : ∀ i, ‖w i‖ ≤ Md) :
    ‖∑ i, m i * inner ℝ (u i) (w i)‖ ≤ (∑ i, m i) * ‖u‖ * Md := by
  have hterm : ∀ i, ‖m i * inner ℝ (u i) (w i)‖ = m i * ‖inner ℝ (u i) (w i)‖ := by
    intro i
    rw [norm_mul, Real.norm_of_nonneg (hm i)]
  calc
    ‖∑ i, m i * inner ℝ (u i) (w i)‖
        ≤ ∑ i, ‖m i * inner ℝ (u i) (w i)‖ := norm_sum_le _ _
    _ = ∑ i, m i * ‖inner ℝ (u i) (w i)‖ := Finset.sum_congr rfl fun i _ => hterm i
    _ ≤ ∑ i, m i * (‖u i‖ * Md) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hm i)
          exact (norm_inner_le_norm (u i) (w i)).trans
            (mul_le_mul_of_nonneg_left (hw i) (norm_nonneg _))
    _ = (∑ i, m i * ‖u i‖) * Md := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    _ ≤ ((∑ i, m i) * ‖u‖) * Md := by
          apply mul_le_mul_of_nonneg_right _ hMd
          calc ∑ i, m i * ‖u i‖
              ≤ ∑ i, m i * ‖u‖ := by
                apply Finset.sum_le_sum
                intro i _
                exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (hm i)
            _ = (∑ i, m i) * ‖u‖ := by rw [Finset.sum_mul]

end Commons.Analysis.InnerProductSpace