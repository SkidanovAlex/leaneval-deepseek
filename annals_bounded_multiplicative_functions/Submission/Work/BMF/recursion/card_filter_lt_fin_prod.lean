import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- The number of strictly ordered pairs `(i, j)` with `i, j : Fin k` is `k.choose 2`, hence
twice that number is `k * (k - 1)`.

This is the elementary count `2 * #{i < j} = k * (k - 1)` used when passing from an ordered
pair count to a count of unordered pairs. -/
theorem card_filter_lt_fin_prod (k : ℕ) :
    ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).card * 2 = k * (k - 1) := by
  -- Identify the unordered-universe product with the full product `univ ×ˢ univ`.
  conv_lhs => rw [← Finset.univ_product_univ]
  -- Mathlib: `#{x ∈ s ×ˢ s | x.1 < x.2} = s.card.choose 2`.
  rw [Finset.card_product_filter_lt]
  simp only [Finset.card_univ, Fintype.card_fin]
  -- It remains to see that `2 * (k.choose 2) = k * (k - 1)`.
  rw [mul_comm, Nat.choose_two_right]
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))

end Work.BMF.recursion
