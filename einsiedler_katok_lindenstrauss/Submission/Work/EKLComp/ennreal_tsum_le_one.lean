import Mathlib

open scoped BigOperators

namespace Work.EKLComp

/-- If a non-negative real sequence has `ENNReal`-total mass at most `1`, then it is summable
as a real series with total sum at most `1`. -/
theorem ennreal_tsum_le_one (a : ℕ → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (h : (∑' i : ℕ, ENNReal.ofReal (a i)) ≤ 1) :
    Summable a ∧ (∑' i : ℕ, a i) ≤ 1 := by
  have hsum_le : ∀ u : Finset ℕ, ∑ i ∈ u, a i ≤ 1 := by
    intro u
    have : ENNReal.ofReal (∑ i ∈ u, a i) ≤ 1 := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha0 i)]
      exact (ENNReal.sum_le_tsum u).trans h
    exact ENNReal.ofReal_le_one.1 this
  refine ⟨summable_of_sum_le ha0 hsum_le, ?_⟩
  exact ENNReal.ofReal_le_one.1
    ((ENNReal.ofReal_tsum_of_nonneg ha0 (summable_of_sum_le ha0 hsum_le)).trans_le h)

end Work.EKLComp
