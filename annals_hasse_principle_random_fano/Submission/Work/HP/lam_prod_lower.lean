import Mathlib
import Submission.Work.HP.lam_basic

namespace Work.HP

open Finset

/-- Lower bound for the product of the first `k` successive minima in terms of `lam L 1` and
`lam L 2`: since `lam L ·` is nondecreasing in the index, the block
`lam L 2, …, lam L k` dominates the constant block `lam L 2, …, lam L 2`. -/
lemma lam_prod_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ rk L) :
    lam L 1 * lam L 2 ^ (k - 1) ≤ ∏ j ∈ Finset.range k, lam L (j + 1) := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `k = 1`: both sides equal `lam L 1`.
    have hk1' : k = 1 := by omega
    subst hk1'; simp
  · have h2rk : 2 ≤ rk L := le_trans hk2 hk
    have h2pos : 0 < lam L 2 := lam_pos L (by norm_num) h2rk
    have hL1 : 0 < lam L 1 := lam_pos L le_rfl (le_trans hk1 hk)
    have hpred : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk1
    -- Split off the `j = 0` factor `lam L 1`.
    have hsplit : (∏ j ∈ Finset.range k, lam L (j + 1))
        = (∏ i ∈ Finset.range (k - 1), lam L (i + 2)) * lam L 1 := by
      conv_lhs => rw [← hpred]
      rw [Finset.prod_range_succ']
    rw [hsplit]
    -- Each remaining factor is at least `lam L 2`.
    have hconst : ∀ i ∈ Finset.range (k - 1), lam L 2 ≤ lam L (i + 2) := by
      intro i hi
      have hi' : i + 2 ≤ k := by have := Finset.mem_range.mp hi; omega
      exact lam_mono L (by omega) (le_trans hi' hk)
    have hprod2 : lam L 2 ^ (k - 1) ≤ ∏ i ∈ Finset.range (k - 1), lam L (i + 2) := by
      rw [show lam L 2 ^ (k - 1) = ∏ _i ∈ Finset.range (k - 1), lam L 2 by
            rw [Finset.prod_const, Finset.card_range]]
      exact Finset.prod_le_prod₀ (fun _ _ => h2pos.le) (fun i hi => hconst i hi)
    calc lam L 1 * lam L 2 ^ (k - 1)
        ≤ lam L 1 * ∏ i ∈ Finset.range (k - 1), lam L (i + 2) :=
            mul_le_mul_of_nonneg_left hprod2 hL1.le
      _ = (∏ i ∈ Finset.range (k - 1), lam L (i + 2)) * lam L 1 := by ring

end Work.HP
