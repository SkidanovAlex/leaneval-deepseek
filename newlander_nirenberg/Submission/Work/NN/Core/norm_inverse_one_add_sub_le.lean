import Mathlib
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le

/-!
# Lipschitz continuity of `X ↦ (1 + X)⁻¹` near `0`

For `X, Y : ℂⁿ →L[ℝ] ℂⁿ` with `‖X‖, ‖Y‖ ≤ 1/4`, both `1 + X` and `1 + Y` are invertible and
the inverse operators are bounded by `2` (Neumann series, see
`isInvertible_one_add_and_inverse_norm_le`).  The resolvent identity

`(1 + X)⁻¹ - (1 + Y)⁻¹ = (1 + X)⁻¹ * (Y - X) * (1 + Y)⁻¹`

(an instance of `a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹` in the ring of endomorphisms) then gives

`‖(1 + X)⁻¹ - (1 + Y)⁻¹‖ ≤ 2 · ‖X - Y‖ · 2 = 4 ‖X - Y‖`.
-/

namespace Work.NN.Core

theorem norm_inverse_one_add_sub_le {n : ℕ} {X Y : Cn n →L[ℝ] Cn n} (hX : ‖X‖ ≤ 1 / 4)
    (hY : ‖Y‖ ≤ 1 / 4) :
    ‖ContinuousLinearMap.inverse (1 + X) - ContinuousLinearMap.inverse (1 + Y)‖ ≤ 4 * ‖X - Y‖ := by
  obtain ⟨hIX, hnX⟩ := isInvertible_one_add_and_inverse_norm_le hX
  obtain ⟨hIY, hnY⟩ := isInvertible_one_add_and_inverse_norm_le hY
  -- `(1 + X)⁻¹` is a right inverse of `1 + X`.
  have hA : (1 + X) * ContinuousLinearMap.inverse (1 + X) = 1 := by
    rw [ContinuousLinearMap.mul_def, hIX.self_comp_inverse, ContinuousLinearMap.one_def]
  -- `(1 + X)⁻¹` is a left inverse of `1 + X`.
  have hA' : ContinuousLinearMap.inverse (1 + X) * (1 + X) = 1 := by
    rw [ContinuousLinearMap.mul_def, hIX.inverse_comp_self, ContinuousLinearMap.one_def]
  have hB : (1 + Y) * ContinuousLinearMap.inverse (1 + Y) = 1 := by
    rw [ContinuousLinearMap.mul_def, hIY.self_comp_inverse, ContinuousLinearMap.one_def]
  -- The resolvent (difference-of-inverses) identity.
  have key : ContinuousLinearMap.inverse (1 + X) * ((1 + Y) - (1 + X)) *
        ContinuousLinearMap.inverse (1 + Y)
      = ContinuousLinearMap.inverse (1 + X) - ContinuousLinearMap.inverse (1 + Y) := by
    rw [mul_sub, hA', sub_mul, mul_assoc, hB, mul_one, one_mul]
  have hdiff : (1 + Y) - (1 + X) = Y - X := by abel
  have hnorm : ‖(1 + Y) - (1 + X)‖ = ‖X - Y‖ := by rw [hdiff, norm_sub_rev]
  calc ‖ContinuousLinearMap.inverse (1 + X) - ContinuousLinearMap.inverse (1 + Y)‖
      = ‖ContinuousLinearMap.inverse (1 + X) * ((1 + Y) - (1 + X)) *
          ContinuousLinearMap.inverse (1 + Y)‖ := by rw [key]
    _ ≤ ‖ContinuousLinearMap.inverse (1 + X) * ((1 + Y) - (1 + X))‖ *
          ‖ContinuousLinearMap.inverse (1 + Y)‖ := norm_mul_le _ _
    _ ≤ (‖ContinuousLinearMap.inverse (1 + X)‖ * ‖(1 + Y) - (1 + X)‖) *
          ‖ContinuousLinearMap.inverse (1 + Y)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (2 * ‖X - Y‖) * 2 := by
        exact mul_le_mul (mul_le_mul hnX (le_of_eq hnorm) (norm_nonneg _) (by norm_num)) hnY
          (norm_nonneg _) (by norm_num)
    _ = 4 * ‖X - Y‖ := by ring

end Work.NN.Core
