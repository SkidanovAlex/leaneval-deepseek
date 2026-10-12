import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.UBBInputs3.MatLoc.Rcorr_even
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.gamma_neg_eq`

The Lieb–Solovej deficit `γ_k = ½Σ_s (prof(s+k) - prof(s))²` is even in the shift `k`.

Since `prof` is even (`prof_neg`) the summand for the shift `-k` is the summand for the
shift `k` evaluated at `-s`, and the summation interval `Icc (-(p+|k|)) (p+|k|)` is
symmetric under `s ↦ -s`; both facts together give the reindexing.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- Reindexing a sum over a symmetric interval `Icc (-a) a` by the involution `s ↦ -s`. -/
lemma sum_Icc_neg_int (f : ℤ → ℝ) (a : ℤ) :
    ∑ s ∈ Finset.Icc (-a) a, f (-s) = ∑ s ∈ Finset.Icc (-a) a, f s := by
  apply Finset.sum_nbij' (fun s => -s) (fun s => -s)
  · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
  · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
  · intro b hb; simp
  · intro b hb; simp
  · intro b hb; rfl

theorem gamma_neg_eq (p : ℕ) (k : ℤ) : Work.UBBInputs3.gamma p (-k) = Work.UBBInputs3.gamma p k := by
  have hA : -(p : ℤ) - |k| = -((p : ℤ) + |k|) := by ring
  simp only [Work.UBBInputs3.gamma, abs_neg, hA]
  congr 1
  rw [← sum_Icc_neg_int
        (fun t => (Work.UBBInputs3.prof p (t + k) - Work.UBBInputs3.prof p t) ^ 2)
        ((p : ℤ) + |k|)]
  exact Finset.sum_congr rfl (fun s _ => by
    rw [show -s + k = -(s + -k) by ring, prof_neg p (s + -k), prof_neg p s])

end Work.UBBInputs3.MatLoc
