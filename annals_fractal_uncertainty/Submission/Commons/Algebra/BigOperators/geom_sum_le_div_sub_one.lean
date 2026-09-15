import Mathlib

namespace Commons.Algebra.BigOperators

lemma geom_sum_le_div_sub_one {x : ℝ} (hx : 1 < x) (r : ℕ) :
    Finset.sum (Finset.range r) (fun k => x ^ k) ≤ x ^ r / (x - 1) := by
  have hx1 : x ≠ 1 := ne_of_gt hx
  rw [geom_sum_eq hx1 r]
  have hpos : 0 < x - 1 := by linarith
  have hle : x ^ r - 1 ≤ x ^ r := by linarith
  exact div_le_div_of_nonneg_right hle (le_of_lt hpos)

end Commons.Algebra.BigOperators
