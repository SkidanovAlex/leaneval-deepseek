import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux

namespace Work.NN.Core

/-- If `X : Cn n →L[ℝ] Cn n` has norm at most `1/4`, then `1 + X` is invertible and the norm of
its inverse is at most `2`.

The inverse is the Neumann series `∑' k, (-X)^k`, whose norm is bounded by
`(1 - ‖X‖)⁻¹ ≤ 4/3 ≤ 2`. -/
theorem isInvertible_one_add_and_inverse_norm_le {n : ℕ} {X : Cn n →L[ℝ] Cn n}
    (hX : ‖X‖ ≤ 1 / 4) :
    (1 + X).IsInvertible ∧ ‖ContinuousLinearMap.inverse (1 + X)‖ ≤ 2 := by
  have hXlt : ‖X‖ < 1 := by linarith [norm_nonneg X]
  have hY : ‖(-X : Cn n →L[ℝ] Cn n)‖ < 1 := by rwa [norm_neg]
  have hZX : (1 - (-X) : Cn n →L[ℝ] Cn n) = 1 + X := by simp [sub_neg_eq_add]
  -- The Neumann series `∑' k, (-X)^k` is a two-sided inverse of `1 + X`.
  have hg1 : (1 + X) * (∑' k : ℕ, (-X) ^ k) = 1 := by
    rw [← hZX]; exact mul_neg_geom_series (-X) hY
  have hg2 : (∑' k : ℕ, (-X) ^ k) * (1 + X) = 1 := by
    rw [← hZX]; exact geom_series_mul_neg (-X) hY
  have hf : (1 + X) ∘SL (∑' k : ℕ, (-X) ^ k) = ContinuousLinearMap.id ℝ (Cn n) := by
    rw [← ContinuousLinearMap.mul_def, hg1, ContinuousLinearMap.one_def]
  have hg' : (∑' k : ℕ, (-X) ^ k) ∘SL (1 + X) = ContinuousLinearMap.id ℝ (Cn n) := by
    rw [← ContinuousLinearMap.mul_def, hg2, ContinuousLinearMap.one_def]
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hf hg', ?_⟩
  rw [ContinuousLinearMap.inverse_eq hf hg']
  have hle := tsum_geometric_le_of_norm_lt_one (-X) hY
  rw [norm_neg] at hle
  have hone : ‖(1 : Cn n →L[ℝ] Cn n)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le
  have htwo : (1 - ‖X‖)⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (a := (1 / 2 : ℝ)) (b := 1 - ‖X‖)
      (by norm_num) (by linarith [norm_nonneg X, hX])
    simpa [one_div] using this
  linarith

end Work.NN.Core
