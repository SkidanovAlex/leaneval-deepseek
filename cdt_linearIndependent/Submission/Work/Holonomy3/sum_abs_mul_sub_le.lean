import Mathlib

namespace Work.Holonomy3

/-- Pointwise bound: if `b p ≥ 0` and `|b p - a p| ≤ 2` for all `p`, then
`|b p * b q - a p * a q| ≤ 2 * b p + 2 * b q + 4`. -/
theorem abs_mul_sub_le_pointwise {N : ℕ} {a b : Fin N → ℝ}
    (hb : ∀ p, 0 ≤ b p) (ha : ∀ p, |b p - a p| ≤ 2) (p q : Fin N) :
    |b p * b q - a p * a q| ≤ 2 * b p + 2 * b q + 4 := by
  have hpq : b p * b q - a p * a q = b p * (b q - a q) + (b p - a p) * a q := by ring
  have hbq : 0 ≤ b q := hb q
  have haq : |a q| ≤ b q + 2 := by
    have h : |a q| ≤ |b q| + |a q - b q| := by
      have h0 := abs_add_le (b q) (a q - b q)
      rwa [show b q + (a q - b q) = a q from by ring] at h0
    rw [abs_of_nonneg hbq, abs_sub_comm] at h
    have hq := ha q
    linarith
  rw [hpq]
  calc |b p * (b q - a q) + (b p - a p) * a q|
      ≤ |b p * (b q - a q)| + |(b p - a p) * a q| := abs_add_le _ _
    _ = b p * |b q - a q| + |b p - a p| * |a q| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hb p)]
    _ ≤ b p * 2 + 2 * (b q + 2) := by
          have h1 : b p * |b q - a q| ≤ b p * 2 := mul_le_mul_of_nonneg_left (ha q) (hb p)
          have h2 : |b p - a p| * |a q| ≤ 2 * (b q + 2) :=
            mul_le_mul (ha p) haq (abs_nonneg _) (by norm_num)
          linarith
    _ = 2 * b p + 2 * b q + 4 := by ring

theorem sum_abs_mul_sub_le {N : ℕ} {a b : Fin N → ℝ} {D : ℝ}
    (hb : ∀ p, 0 ≤ b p) (hsum : ∑ p, b p = D) (ha : ∀ p, |b p - a p| ≤ 2) :
    ∑ p, ∑ q, |b p * b q - a p * a q| ≤ 4 * (N : ℝ) * D + 4 * (N : ℝ) ^ 2 := by
  calc ∑ p : Fin N, ∑ q : Fin N, |b p * b q - a p * a q|
      ≤ ∑ p : Fin N, ∑ q : Fin N, (2 * b p + 2 * b q + 4) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        exact abs_mul_sub_le_pointwise hb ha p q
    _ = 4 * (N : ℝ) * D + 4 * (N : ℝ) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum, hsum]
        ring

end Work.Holonomy3
