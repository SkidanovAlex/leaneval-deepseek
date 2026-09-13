import Mathlib

namespace Commons.Algebra.Order

theorem negPart_mul_le_of_sum_mul_nonneg {ι : Type*} [Fintype ι] {lam xi : ι → ℝ} {a c c' : ℝ} (hc : 0 < c) (hxi : ∀ i, c ≤ xi i) (hxi' : ∀ i, xi i ≤ c') (hlam : ∀ i, lam i ≤ a) (ha : 0 ≤ a) (hsum : 0 ≤ ∑ i, lam i * xi i) : (∑ i, max (-(lam i)) 0) * c ≤ (Fintype.card ι : ℝ) * c' * a := by
  have hsplit : ∑ i, lam i * xi i
      = ∑ i, max (lam i) 0 * xi i - ∑ i, max (-(lam i)) 0 * xi i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  have hle : ∑ i, max (-(lam i)) 0 * xi i ≤ ∑ i, max (lam i) 0 * xi i := by
    linarith [hsum, hsplit]
  have hnc : (∑ i, max (-(lam i)) 0) * c ≤ ∑ i, max (-(lam i)) 0 * xi i := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hxi i) (le_max_right _ _)
  have hpc : ∑ i, max (lam i) 0 * xi i ≤ (Fintype.card ι : ℝ) * (a * c') := by
    calc ∑ i, max (lam i) 0 * xi i ≤ ∑ i, a * c' := by
          apply Finset.sum_le_sum
          intro i _
          have hxi0 : 0 ≤ xi i := le_trans (le_of_lt hc) (hxi i)
          exact le_trans (mul_le_mul_of_nonneg_right (max_le (hlam i) ha) hxi0)
            (mul_le_mul_of_nonneg_left (hxi' i) ha)
      _ = (Fintype.card ι : ℝ) * (a * c') := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfinal : (∑ i, max (-(lam i)) 0) * c ≤ (Fintype.card ι : ℝ) * (a * c') :=
    le_trans hnc (le_trans hle hpc)
  nlinarith [hfinal]

end Commons.Algebra.Order
