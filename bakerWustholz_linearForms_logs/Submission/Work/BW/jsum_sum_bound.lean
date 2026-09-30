import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Double triangle inequality: a sum over `Z × {0,…,Tp}` whose summands all have norm at most `c`
has norm at most `|Z|(Tp+1)c`. -/
lemma jsum_sum_bound (Z : Finset ℤ) (Tp : ℕ) (b : ℤ → ℕ → ℂ) (c : ℝ)
    (hb : ∀ l ∈ Z, ∀ m ∈ Finset.range (Tp + 1), ‖b l m‖ ≤ c) :
    ‖∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), b l m‖ ≤ (Z.card : ℝ) * (Tp + 1) * c := by
  calc ‖∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), b l m‖
      ≤ ∑ l ∈ Z, ‖∑ m ∈ Finset.range (Tp + 1), b l m‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), ‖b l m‖ := by
        apply Finset.sum_le_sum
        intro l hl
        exact norm_sum_le _ _
    _ ≤ ∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), c := by
        apply Finset.sum_le_sum
        intro l hl
        apply Finset.sum_le_sum
        intro m hm
        exact hb l hl m hm
    _ = (Z.card : ℝ) * (Tp + 1) * c := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          nsmul_eq_mul]
        push_cast
        ring

end Work.BW
