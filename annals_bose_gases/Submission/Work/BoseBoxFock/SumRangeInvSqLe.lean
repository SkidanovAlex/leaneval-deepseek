import Mathlib.Analysis.PSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- `Finset.range (m+1)` splits off the `0` term from `Finset.Ioo 0 (m+1)`. -/
private lemma range_succ_eq_insert_Ioo (m : ℕ) :
    Finset.range (m + 1) = insert 0 (Finset.Ioo 0 (m + 1)) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
  omega

/--
The `n`-th partial sum of the (super-)summable series `∑ 1/j²` is at most `2`.
The `j = 0` term contributes `0` (`1/0² = 0`), and the remaining terms are bounded by
Mathlib's `sum_Ioo_inv_sq_le` with `k = 0`: `∑_{0 < j < n} 1/j² ≤ 2/(0+1) = 2`.
-/
theorem SumRangeInvSqLe (n : ℕ) : ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) ^ 2) ≤ 2 := by
  rcases n with _ | m
  · simp
  rw [range_succ_eq_insert_Ioo m, Finset.sum_insert (by simp [Finset.mem_Ioo])]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add]
  have h := sum_Ioo_inv_sq_le (α := ℝ) (k := 0) (n := m + 1)
  simpa [one_div] using h

end Work.BoseBoxFock
