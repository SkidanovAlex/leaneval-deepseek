import Mathlib
import Submission.Commons.Analysis.Complex.pow_sum_norm_le_root

namespace Commons.Analysis.Complex

theorem pow_sum_norm_le_root_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h : ∀ n : ℕ, 0 < n → ‖∑ i, (z i) ^ n‖ ≤ a * b ^ n) :
    ‖∑ i, z i‖ ≤ (Fintype.card ι : ℝ) * b := by
  have hroot : ∀ i, ‖z i‖ ≤ b := pow_sum_norm_le_root z ha hb h
  calc ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := norm_sum_le Finset.univ z
    _ ≤ ∑ _i : ι, b := Finset.sum_le_sum (fun i _ => hroot i)
    _ = (Fintype.card ι : ℝ) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Commons.Analysis.Complex
