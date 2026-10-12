import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

/-- Reindex a finite sum over an integer interval under a constant shift `s ↦ s + k`. -/
lemma sum_Icc_addConst (G : ℤ → ℝ) (a b k : ℤ) :
    (∑ s ∈ Finset.Icc a b, G (s + k)) = ∑ t ∈ Finset.Icc (a + k) (b + k), G t := by
  refine Finset.sum_bij (fun s _ => s + k) ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
  · intro s1 hs1 s2 hs2 h; omega
  · intro t ht; refine ⟨t - k, ?_, ?_⟩ <;> simp only [Finset.mem_Icc] at ht ⊢ <;> omega
  · intro s hs; rfl

theorem gamma_sum_shift (p : ℕ) (k : ℤ) {f : ℤ → ℝ}
    (hsupp : ∀ s, s ∉ Finset.Icc (-(p:ℤ)) (p:ℤ) → f s = 0) :
    (∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), (f (s+k))^2)
      = ∑ t ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), (f t)^2 := by
  rw [sum_Icc_addConst (fun t => (f t)^2) (-(p:ℤ) - |k|) ((p:ℤ) + |k|) k]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro t ht
    simp only [Finset.mem_Icc] at ht ⊢
    constructor
    · have := le_abs_self k; linarith
    · have := neg_le_abs k; linarith
  · intro t _ hnt
    rw [hsupp t hnt]; ring

end Work.UBBInputs3.MatLoc
