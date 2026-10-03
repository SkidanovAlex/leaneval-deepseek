import Mathlib

namespace Work.FIArea7

theorem pairW_bilinear_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (K : ι → ι → ℝ) (f : ι → ℝ)
    (hK : ∀ a b, 0 ≤ K a b) (hsym : ∀ a b, K a b = K b a) :
    (∑ a ∈ s, ∑ b ∈ s, K a b * f a * f b)
      ≤ ∑ a ∈ s, f a ^ 2 * (∑ b ∈ s, K a b) := by
  -- Rewrite the RHS as the "diagonal" double sum P = ∑∑ K_ab f_a^2.
  have hE1 : (∑ a ∈ s, f a ^ 2 * (∑ b ∈ s, K a b)) = ∑ a ∈ s, ∑ b ∈ s, K a b * f a ^ 2 := by
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b hb
    ring
  -- The "off-diagonal-swapped" double sum Q = ∑∑ K_ab f_b^2 equals P, by symmetry.
  have hE2 : (∑ a ∈ s, ∑ b ∈ s, K a b * f b ^ 2) = ∑ a ∈ s, ∑ b ∈ s, K a b * f a ^ 2 := by
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro b hb
    rw [hsym b a]
  -- ∑∑ K_ab (f_a^2 + f_b^2) = P + Q.
  have hE3 : (∑ a ∈ s, ∑ b ∈ s, K a b * (f a ^ 2 + f b ^ 2))
      = (∑ a ∈ s, ∑ b ∈ s, K a b * f a ^ 2) + (∑ a ∈ s, ∑ b ∈ s, K a b * f b ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b hb
    ring
  -- Pointwise AM-GM: 2 K_ab f_a f_b ≤ K_ab (f_a^2 + f_b^2).
  have hkey : (∑ a ∈ s, ∑ b ∈ s, 2 * (K a b * f a * f b))
      ≤ ∑ a ∈ s, ∑ b ∈ s, K a b * (f a ^ 2 + f b ^ 2) := by
    apply Finset.sum_le_sum; intro a ha
    apply Finset.sum_le_sum; intro b hb
    nlinarith [mul_nonneg (hK a b) (sq_nonneg (f a - f b))]
  -- Push the factor 2 inside the double sum.
  have hL : 2 * (∑ a ∈ s, ∑ b ∈ s, K a b * f a * f b)
      = ∑ a ∈ s, ∑ b ∈ s, 2 * (K a b * f a * f b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum]
  have hC : 2 * (∑ a ∈ s, ∑ b ∈ s, K a b * f a * f b)
      ≤ (∑ a ∈ s, ∑ b ∈ s, K a b * f a ^ 2) + (∑ a ∈ s, ∑ b ∈ s, K a b * f b ^ 2) := by
    rw [hL, ← hE3]; exact hkey
  linarith [hC, hE1, hE2]

end Work.FIArea7
