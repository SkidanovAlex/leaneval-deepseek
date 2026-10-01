import Mathlib

namespace Work.LinnikAreas

theorem epsPowSumReNonneg {ε : ℂ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) (k : ℕ) :
    0 ≤ (∑ j ∈ Finset.range (k + 1), ε ^ j).re ∧ (∑ j ∈ Finset.range (k + 1), ε ^ j).im = 0 := by
  rcases hε with rfl | rfl | rfl
  · -- ε = 0 : the sum is 1 + 0 + ⋯ + 0 = 1
    have h : (∑ j ∈ Finset.range (k + 1), (0:ℂ) ^ j) = 1 := by
      induction k with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; simp
    rw [h]; simp
  · -- ε = 1 : the sum is k + 1, a nonnegative real number
    have h : (∑ j ∈ Finset.range (k + 1), (1:ℂ) ^ j) = (k : ℂ) + 1 := by
      simp
    rw [h]
    constructor
    · simp; positivity
    · simp
  · -- ε = -1 : the sum equals (1 + (-1)^k)/2, i.e. 1 or 0
    have h : (∑ j ∈ Finset.range (k + 1), (-1:ℂ) ^ j) = (1 + (-1:ℂ)^k)/2 := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
    rw [h]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]; norm_num
    · rw [hk.neg_one_pow]; norm_num

end Work.LinnikAreas
