import Mathlib
import Submission.Work.TMC14Core.Weyl

/-!
# `TMC14Core.InvCountSucc`

The recursion for the inversion number `invCount` of a two-letter word over the
alphabet `{(true,true), (false,true)} = {U, V}` under appending a letter at the
front:

`invCount (n+1) f = invCount n (fun i => f i.succ)
    + (if f 0 = U then #{V-letters among the tail} else 0)`.

Here `invCount n f` counts the pairs `i < j` whose letters are `U` then `V`.
Peeling off the first letter therefore contributes, when it is a `U`, exactly the
number of `V`-letters in the tail; the remaining pairs are exactly the inversion
pairs of the tail.

The combinatorial heart is the bijection `j ↦ j.pred` between the non-zero
indices of `Fin (n+1)` and `Fin n` (lemma `card_filter_lt_succ`).
-/

open Finset

noncomputable section

namespace Work.TMC14Core

/-- Cardinality transfer `Fin (n+1) → Fin n` for `filter` sets cut by a lower
bound `c` on the value: an index `j : Fin (n+1)` with `c < j.val` corresponds to
`j.pred : Fin n` with `c ≤ (j.pred).val` (and conversely). -/
lemma card_filter_lt_succ (n : ℕ) (P : Fin (n + 1) → Prop) [DecidablePred P] (c : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => P j ∧ c < j.val)).card =
      ((Finset.univ : Finset (Fin n)).filter (fun k => P k.succ ∧ c ≤ k.val)).card := by
  apply Finset.card_bij (fun j hj => Fin.pred j (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact fun h => by
        have : (j : ℕ) = 0 := by rw [h]; exact Fin.val_zero (n+1)
        omega))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, ?_⟩
    · rw [Fin.succ_pred]; exact hj.1
    · rw [Fin.val_pred]; omega
  · intro j1 hj1 j2 hj2 heq
    have h := congrArg Fin.succ heq
    simp only [Fin.succ_pred] at h
    exact h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨b.succ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hb.1, by rw [Fin.val_succ]; omega⟩
    · simp only [Fin.pred_succ]

/-- The number of `V = (false,true)` letters in positions `1, …, n` of `f` is
the number of `V`-letters in the tail `f ∘ succ`. -/
lemma invCount_aux_cnt (n : ℕ) (f : Fin (n + 1) → Bool × Bool) :
    ((Finset.univ : Finset (Fin (n+1))).filter
        (fun j => f j = (false,true) ∧ (0 : Fin (n + 1)).val < j.val)).card
      = cnt false true n (fun i => f i.succ) := by
  apply Finset.card_bij (fun j hj => Fin.pred j (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact fun h => by
        rw [h] at hj
        simp only [Fin.val_zero] at hj
        omega))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [Fin.succ_pred]
    exact hj.1
  · intro j1 hj1 j2 hj2 heq
    have h := congrArg Fin.succ heq
    simp only [Fin.succ_pred] at h
    exact h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨b.succ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hb, ?_⟩
      rw [Fin.val_succ, Fin.val_zero]
      omega
    · simp only [Fin.pred_succ]

/-- Transfer of the inner count: the `V`-positions after `i.succ` in `Fin (n+1)`
are the `V`-positions after `i` in the tail `Fin n`. -/
lemma invCount_aux_inner (n : ℕ) (f : Fin (n + 1) → Bool × Bool) (i : Fin n) :
    ((Finset.univ : Finset (Fin (n+1))).filter
        (fun j => f j = (false,true) ∧ (i.succ).val < j.val)).card
      = ((Finset.univ : Finset (Fin n)).filter
        (fun k => f k.succ = (false,true) ∧ i.val < k.val)).card := by
  apply Finset.card_bij (fun j hj => Fin.pred j (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact fun h => by
        rw [h] at hj
        simp only [Fin.val_zero] at hj
        omega))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, ?_⟩
    · rw [Fin.succ_pred]; exact hj.1
    · rw [Fin.val_pred, Fin.val_succ] at *; omega
  · intro j1 hj1 j2 hj2 heq
    have h := congrArg Fin.succ heq
    simp only [Fin.succ_pred] at h
    exact h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨b.succ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hb.1, ?_⟩
      rw [Fin.val_succ, Fin.val_succ]
      omega
    · simp only [Fin.pred_succ]

/-- `invCount` as a plain sum over `Fin n`. -/
lemma invCount_eq_sum (n : ℕ) (f : Fin n → Bool × Bool) :
    invCount n f = ∑ i : Fin n, (if f i = (true,true) then
      ((Finset.univ : Finset (Fin n)).filter
        (fun j => f j = (false,true) ∧ i.val < j.val)).card else 0) := by
  unfold invCount
  rw [Finset.sum_filter]

/-- The contribution of the tail `Fin n` to `invCount (n+1) f`. -/
lemma invCount_succ_sum (n : ℕ) (f : Fin (n + 1) → Bool × Bool) :
    (∑ i : Fin n, (if f i.succ = (true,true) then
        ((Finset.univ : Finset (Fin (n+1))).filter
          (fun j => f j = (false,true) ∧ (i.succ).val < j.val)).card else 0))
      = invCount n (fun i => f i.succ) := by
  unfold invCount
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i.succ = (true,true)
  · simp only [h, if_true, invCount_aux_inner]
  · simp only [h, if_false]

theorem InvCountSucc (n : ℕ) (f : Fin (n + 1) → Bool × Bool) :
    invCount (n + 1) f = invCount n (fun i => f i.succ) +
      (if f 0 = (true, true) then cnt false true n (fun i => f i.succ) else 0) := by
  rw [invCount_eq_sum (n+1) f]
  rw [Fin.sum_univ_succ]
  simp only [invCount_aux_cnt n f]
  rw [invCount_succ_sum n f]
  exact Nat.add_comm _ _

end Work.TMC14Core
