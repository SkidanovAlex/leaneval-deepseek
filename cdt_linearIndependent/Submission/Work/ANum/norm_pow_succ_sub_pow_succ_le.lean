import Mathlib

namespace Work.ANum

theorem norm_pow_succ_sub_pow_succ_le {x y : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * r ^ n * ‖x - y‖ := by
  have hr : 0 ≤ r := le_trans (norm_nonneg x) hx
  have hℓ : (∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)) * (x - y)
      = x ^ (n + 1) - y ^ (n + 1) := by
    have h := (Commute.all x y).geom_sum₂_mul (n + 1)
    simpa [Nat.add_sub_cancel] using h
  have hterm : ∀ i ∈ Finset.range (n + 1), ‖x ^ i * y ^ (n - i)‖ ≤ r ^ n := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖x‖ ^ i * ‖y‖ ^ (n - i) ≤ r ^ i * r ^ (n - i) := by
          gcongr
      _ = r ^ n := by rw [← pow_add]; congr 1; omega
  have hsum : ‖∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)‖ ≤ ((n : ℝ) + 1) * r ^ n := by
    calc ‖∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)‖
        ≤ ∑ i ∈ Finset.range (n + 1), ‖x ^ i * y ^ (n - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), r ^ n := Finset.sum_le_sum hterm
      _ = ((n : ℝ) + 1) * r ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc ‖x ^ (n + 1) - y ^ (n + 1)‖
      = ‖(∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)) * (x - y)‖ := by rw [hℓ]
    _ = ‖∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)‖ * ‖x - y‖ := norm_mul _ _
    _ ≤ (((n : ℝ) + 1) * r ^ n) * ‖x - y‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ = ((n : ℝ) + 1) * r ^ n * ‖x - y‖ := by ring

end Work.ANum
