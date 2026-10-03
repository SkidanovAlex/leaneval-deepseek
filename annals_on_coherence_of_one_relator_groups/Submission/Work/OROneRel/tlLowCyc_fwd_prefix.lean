/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# A positively-oriented word of the low window is a forward cycle prefix

For coprime `p, q ≥ 1` the low window `[0, p+q-1]` of the level graph of the `Z`-cover of the
two-letter band `a^p b^q` (weight `tlW p q`, `a ↦ q`, `b ↦ -p`) is a single cycle, and every level
`i` has a *unique* outgoing window edge: the `a`-edge below `p`, the `b`-edge at or above `p`
(`letter_pos_winE`, `tlLowCycStep.lean`).

Consequently a word all of whose letters are positive and all of whose decorated edges lie in the
window must spell the window cycle *forward* from its starting level: it is the forward cycle
prefix `cycFwdList p q k L.length` at the index `k = cycLevel p q k` fixed by the decoration.
This is the positive half of the combinatorial crux of
`Submission/Work/OROneRel/tlWin_low_zpowers_lemma.lean`, where it is applied with `k = 0` to the
reduced word of an element of the window subgroup.

The proof is an induction on the list, shifting the running index by one at each step
(`cycFwdList_succ`), the head letter being forced by `head_pos_letter` and the level advance by
`cycLevel_add_tlW_cycLetter`.
-/
import Mathlib
import Submission.Work.OROneRel.tlLowCycStep

namespace Work.OROneRel

/-- **The forward cycle prefix, one step at a time.**  Reading the prefix of length `m+1` from the
index `k` is reading the letter of the cycle at `k` and then the prefix of length `m` from the
index `k+1`. -/
theorem cycFwdList_succ (p q : ℕ) (k : ℤ) (m : ℕ) :
    cycFwdList p q k (m + 1) = (cycLetter p q k, true) :: cycFwdList p q (k + 1) m := by
  simp only [cycFwdList]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro j _
    simp [Function.comp]
    ring_nf

/-- **A positively oriented word of the low window is a forward cycle prefix** (auxiliary form,
with the starting index `k` generalised over the induction). -/
theorem tlLowCyc_fwd_prefix_aux (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ (k : ℤ) (L : List (Fin 2 × Bool)),
      (∀ l ∈ L, l.2 = true) →
      (∀ e ∈ decor (tlW p q) (cycLevel p q k) L,
        coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1)) →
      L = cycFwdList p q k L.length := by
  intro k L
  induction L generalizing k with
  | nil => intro _ _; simp [cycFwdList]
  | cons l t ih =>
    obtain ⟨a, b⟩ := l
    intro htrue hwin
    have hb : b = true := htrue (a, b) (by simp)
    subst hb
    -- the head letter is forced to be the letter of the cycle at the index `k`
    have haeq : a = cycLetter p q k := head_pos_letter p q hp hq hwin
    have htrue_t : ∀ x ∈ t, x.2 = true := fun x hx => htrue x (List.mem_cons_of_mem _ hx)
    -- the running level after the head is the level of the cycle at the index `k+1`
    have hlev : cycLevel p q k + tlW p q a = cycLevel p q (k + 1) := by
      rw [haeq]; exact cycLevel_add_tlW_cycLetter p q hp hq k
    have htail : ∀ e ∈ decor (tlW p q) (cycLevel p q (k + 1)) t,
        coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) := by
      intro e he
      refine hwin e ?_
      rw [show decor (tlW p q) (cycLevel p q k) ((a, true) :: t)
            = ((a, cycLevel p q k), true)
                :: decor (tlW p q) (cycLevel p q k + tlW p q a) t from rfl,
        hlev]
      exact List.mem_cons_of_mem _ he
    have ht := ih (k + 1) htrue_t htail
    rw [List.length_cons, cycFwdList_succ, haeq]
    simp only [List.cons.injEq, true_and]
    exact ht

theorem tlLowCyc_fwd_prefix (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ)
    (L : List (Fin 2 × Bool))
    (htrue : ∀ l ∈ L, l.2 = true)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) (Work.OROneRel.cycLevel p q k) L,
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) + (q : ℤ) - 1)) :
    L = Work.OROneRel.cycFwdList p q k L.length :=
  tlLowCyc_fwd_prefix_aux p q hp hq k L htrue hwin

end Work.OROneRel
