import Mathlib

namespace Work.EQ.Fatou

theorem tsum_pow_sub_sq_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (N : ℕ)
    {r s : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑' n : ℕ, a n * (r ^ n - s ^ n) ^ 2
      ≤ ∑ n ∈ Finset.range N, a n * (r ^ n - s ^ n) ^ 2
        + (∑' n : ℕ, a n - ∑ n ∈ Finset.range N, a n) := by
  have hb0 : ∀ n, 0 ≤ (r ^ n - s ^ n) ^ 2 := fun n => sq_nonneg _
  have hb1 : ∀ n, (r ^ n - s ^ n) ^ 2 ≤ 1 := by
    intro n
    have hrn : 0 ≤ r ^ n := pow_nonneg hr n
    have hrn1 : r ^ n ≤ 1 := pow_le_one₀ hr hr1
    have hsn : 0 ≤ s ^ n := pow_nonneg hs0 n
    have hsn1 : s ^ n ≤ 1 := pow_le_one₀ hs0 hs1
    rw [sq_le_one_iff_abs_le_one, abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hsum_b : Summable (fun n => a n * (r ^ n - s ^ n) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (ha n) (hb0 n))
      (fun n => mul_le_of_le_one_right (ha n) (hb1 n)) hs
  have hA : ∑' n : ℕ, a (n + N) = (∑' n : ℕ, a n) - ∑ n ∈ Finset.range N, a n := by
    have h := hs.sum_add_tsum_nat_add N
    linarith
  have htail : ∑' n : ℕ, a (n + N) * (r ^ (n + N) - s ^ (n + N)) ^ 2
      ≤ ∑' n : ℕ, a (n + N) := by
    refine Summable.tsum_le_tsum (fun n => mul_le_of_le_one_right (ha (n + N)) (hb1 (n + N)))
      ((summable_nat_add_iff N).mpr hsum_b) ((summable_nat_add_iff N).mpr hs)
  calc ∑' n : ℕ, a n * (r ^ n - s ^ n) ^ 2
      = (∑ n ∈ Finset.range N, a n * (r ^ n - s ^ n) ^ 2)
          + ∑' n : ℕ, a (n + N) * (r ^ (n + N) - s ^ (n + N)) ^ 2 :=
        (hsum_b.sum_add_tsum_nat_add N).symm
    _ ≤ (∑ n ∈ Finset.range N, a n * (r ^ n - s ^ n) ^ 2)
          + ∑' n : ℕ, a (n + N) := by linarith [htail]
    _ = (∑ n ∈ Finset.range N, a n * (r ^ n - s ^ n) ^ 2)
          + ((∑' n : ℕ, a n) - ∑ n ∈ Finset.range N, a n) := by rw [hA]

end Work.EQ.Fatou
