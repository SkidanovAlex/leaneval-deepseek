import Mathlib
import Submission.Work.WilG4c.AlSliceBase

namespace Work.WilG4c

/-!
# Cardinality bound for the criterion index set

`Work.WilkG4c.critIdx n k` is the index set of the conditions (C1) of the punctured-limit
criterion: the sigma over the orders `m : Fin k` of the counts vectors
`Fin (n + 1) → Fin (m.val + 1)`.  Hence

  `#(critIdx n k) = Σ_{m < k} (m + 1)^{n+1} ≤ k · k^{n+1} ≤ k · k^{n+1} + 1`,

the bound being polynomial in `k`, as required by the `Ω`-machine bookkeeping.
-/

/-- The cardinality of the sigma type of counts vectors: each order `m < k` contributes
`(m + 1)^{n+1}` counts vectors. -/
theorem critIdx_card (n k : ℕ) :
    (Work.WilkG4c.critIdx n k).card = ∑ m : Fin k, (m.val + 1) ^ (n + 1) := by
  rw [Work.WilkG4c.critIdx, Finset.card_sigma]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.card_univ, Fintype.card_fun]
  simp

/-- **Cardinality bound for the criterion index set.**  The number of conditions (C1) at order
`≤ k` is at most `k · k^{n+1} + 1`: there are `k` orders and, at each of them, at most
`k^{n+1}` counts vectors. -/
theorem CritIdxCardLe (n k : ℕ) : (Work.WilkG4c.critIdx n k).card ≤ k * k ^ (n + 1) + 1 := by
  rw [critIdx_card]
  have hterm : ∀ m : Fin k, (m.val + 1) ^ (n + 1) ≤ k ^ (n + 1) :=
    fun m => Nat.pow_le_pow_left (Nat.succ_le_of_lt m.isLt) _
  calc ∑ m : Fin k, (m.val + 1) ^ (n + 1)
      ≤ ∑ _m : Fin k, k ^ (n + 1) := Finset.sum_le_sum fun m _ => hterm m
    _ = k * k ^ (n + 1) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ k * k ^ (n + 1) + 1 := Nat.le_add_right _ _

end Work.WilG4c
