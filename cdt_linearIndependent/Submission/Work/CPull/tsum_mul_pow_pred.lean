import Mathlib

namespace Work.CPull

theorem tsum_mul_pow_pred (c : ℕ → ℂ) (y : ℂ)
    (h : Summable fun n : ℕ => (n : ℂ) * c n * y ^ (n - 1)) :
    ∑' n : ℕ, (n : ℂ) * c n * y ^ (n - 1)
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n := by
  rw [Summable.tsum_eq_zero_add h]
  have h0 : ((0 : ℕ) : ℂ) * c 0 * y ^ (0 - 1) = 0 := by simp
  rw [h0, zero_add]
  exact tsum_congr fun n => by rw [Nat.add_sub_cancel]

end Work.CPull
