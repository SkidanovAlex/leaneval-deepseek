import Mathlib

namespace Work.EQ

theorem geom_sum_sq {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, (κ ^ 2) ^ k ≤ 1 / (1 - κ ^ 2) := by
  have hr0 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hr1 : κ ^ 2 < 1 := by nlinarith [h0, h1]
  have hsummable : Summable fun k : ℕ => (κ ^ 2) ^ k :=
    summable_geometric_of_lt_one hr0 hr1
  have h := hsummable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg hr0 i)
  simpa [one_div, tsum_geometric_of_lt_one hr0 hr1] using h

end Work.EQ
