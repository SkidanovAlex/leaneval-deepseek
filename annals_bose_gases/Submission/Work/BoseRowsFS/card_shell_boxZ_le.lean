import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowsFS.SumExpDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

/-- The `k`-th shell `boxZ k \ boxZ (k-1)` has `(2k+1)³ - (2k-1)³ = 24k² + 2 ≤ 26k²` elements
for `k ≥ 1`.  (For `k ≥ 1` the shell is precisely the set of vectors of max-norm exactly `k`,
so its cardinality is the difference of the two box cardinalities `card_boxZ`.) -/
theorem card_shell_boxZ_le (k : ℕ) (hk : 1 ≤ k) :
    ((Work.BoseRowsFS.boxZ k) \ (Work.BoseRowsFS.boxZ (k - 1))).card ≤ 26 * k ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hsub : boxZ m ⊆ boxZ (m + 1) := boxZ_subset (m + 1)
  rw [Nat.add_sub_cancel]
  rw [Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr hsub]
  rw [card_boxZ, card_boxZ]
  rw [Nat.sub_le_iff_le_add]
  nlinarith [sq_nonneg (m : ℤ)]

end Work.BoseRowsFS
