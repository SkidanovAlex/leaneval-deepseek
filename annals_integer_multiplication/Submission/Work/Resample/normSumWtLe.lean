import Mathlib

namespace Work.Resample

theorem normSumWtLe (L p : ℕ) (W : ℕ → ℤ) (ζ : ℕ → ℂ) (β : ℕ → ℝ)
    (hβ : ∀ i ∈ Finset.range L, 0 ≤ β i)
    (hW : ∀ i ∈ Finset.range L, |(W i : ℝ)| ≤ (2 : ℝ) ^ p * β i + 2)
    (hζ : ∀ i ∈ Finset.range L, ‖ζ i‖ ≤ (2 : ℝ) ^ p)
    (hrow : ∑ i ∈ Finset.range L, β i ≤ 3 / 4) :
    ‖∑ i ∈ Finset.range L, (W i : ℂ) * ζ i‖ ≤
      (2 : ℝ) ^ p * ((3 / 4) * (2 : ℝ) ^ p + 2 * (L : ℝ)) := by
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hstep : ∀ i ∈ Finset.range L,
      ‖(W i : ℂ) * ζ i‖ ≤ ((2 : ℝ) ^ p * β i + 2) * (2 : ℝ) ^ p := by
    intro i hi
    rw [norm_mul, Complex.norm_intCast]
    exact mul_le_mul (hW i hi) (hζ i hi) (norm_nonneg _)
      (add_nonneg (mul_nonneg h2p (hβ i hi)) (by norm_num))
  have hsum : ∑ i ∈ Finset.range L, ((2 : ℝ) ^ p * β i + 2) * (2 : ℝ) ^ p =
      (2 : ℝ) ^ p * ((2 : ℝ) ^ p * ∑ i ∈ Finset.range L, β i + 2 * (L : ℝ)) := by
    rw [← Finset.sum_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have key : (2 : ℝ) ^ p * ∑ i ∈ Finset.range L, β i ≤ (3 / 4) * (2 : ℝ) ^ p := by
    have := mul_le_mul_of_nonneg_left hrow h2p
    linarith
  calc ‖∑ i ∈ Finset.range L, (W i : ℂ) * ζ i‖
      ≤ ∑ i ∈ Finset.range L, ‖(W i : ℂ) * ζ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range L, ((2 : ℝ) ^ p * β i + 2) * (2 : ℝ) ^ p :=
        Finset.sum_le_sum hstep
    _ = (2 : ℝ) ^ p * ((2 : ℝ) ^ p * ∑ i ∈ Finset.range L, β i + 2 * (L : ℝ)) := hsum
    _ ≤ (2 : ℝ) ^ p * ((3 / 4) * (2 : ℝ) ^ p + 2 * (L : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ h2p
        linarith

end Work.Resample
