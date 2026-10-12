import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.LatticeBoxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cardinality of the `k`-th lattice shell

`shell k = box k \ box (k-1)` is the set of multi-indices `m : Fin 3 → ℤ` whose sup-norm
`K m` is exactly `k`.  In fact `box k` has cardinality `(2k+1)³` and `box (k-1)` has
cardinality `(2k-1)³` (for `k ≥ 1`), so the shell has exactly

    (2k+1)³ - (2k-1)³ = 24 k² + 2

elements.  We only need the upper bound `≤ 24 k² + 2`.
-/

namespace Work.BoseBoxFock

open Finset

/-- The integer interval `[-k, k]` has `2k + 1` elements. -/
lemma shellCard_Icc_int (k : ℕ) : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
  rw [Int.card_Icc]
  have h : ((k : ℤ) + 1 - (-(k : ℤ))) = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The box `[-k,k]³` of multi-indices has `(2k+1)³` elements. -/
lemma shellCard_box_card (k : ℕ) : (box k).card = (2 * k + 1) ^ 3 := by
  rw [box, Fintype.card_piFinset]
  simp only [shellCard_Icc_int, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The `k`-th shell has at most `24 k² + 2` elements.  (In fact it has exactly that many.) -/
theorem ShellCard {k : ℕ} (hk : 1 ≤ k) : (shell k).card ≤ 24 * k ^ 2 + 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsub : box j ⊆ box (j + 1) := box_mono (Nat.le_succ j)
  have hid : j + 1 - 1 = j := rfl
  rw [shell, hid, Finset.card_sdiff_of_subset hsub, shellCard_box_card, shellCard_box_card]
  rw [Nat.sub_le_iff_le_add]
  nlinarith [sq_nonneg (j : ℤ)]

end Work.BoseBoxFock
