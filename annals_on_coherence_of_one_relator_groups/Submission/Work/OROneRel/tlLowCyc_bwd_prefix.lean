import Mathlib
import Submission.Work.OROneRel.tlLowCycStep

namespace Work.OROneRel

/-! # A negative window word is a backward cycle prefix

If every letter of `L` is negative (`l.2 = false`) and the decoration of `L` from the cycle index
`k` never leaves the low window `[0, p+q-1]`, then `L` is exactly the backward cycle prefix
`cycBwdList p q k L.length`.

The proof is by induction on `L`, peeling the head letter: `head_neg_letter` forces the head to be
`(cycLetter p q (k-1), false)`, the running level drops to `cycLevel p q (k-1)`, and the induction
hypothesis applies to the tail.  The list arithmetic that makes the induction go through is
`cycBwdList_succ`. -/

/-- Peeling the head of a backward cycle prefix. -/
lemma cycBwdList_succ (p q : ℕ) (k : ℤ) (n : ℕ) :
    cycBwdList p q k (n+1) = (cycLetter p q (k-1), false) :: cycBwdList p q (k-1) n := by
  simp only [cycBwdList, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    congr 2
    push_cast
    ring

theorem tlLowCyc_bwd_prefix (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ)
    (L : List (Fin 2 × Bool))
    (hfalse : ∀ l ∈ L, l.2 = false)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) (Work.OROneRel.cycLevel p q k) L,
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) + (q : ℤ) - 1)) :
    L = Work.OROneRel.cycBwdList p q k L.length := by
  have key : ∀ (L : List (Fin 2 × Bool)) (k : ℤ),
      (∀ l ∈ L, l.2 = false) →
      (∀ e ∈ decor (tlW p q) (cycLevel p q k) L,
        coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1)) →
      L = cycBwdList p q k L.length := by
    intro L
    induction L with
    | nil => intro k _ _; simp [cycBwdList]
    | cons hd t ih =>
      intro k hfalse hwin
      rcases hd with ⟨a, b⟩
      cases b with
      | false =>
        -- the head letter is forced by the window
        have ha : a = cycLetter p q (k - 1) := head_neg_letter p q hp hq hwin
        -- the running level after the head letter is the previous cycle index
        have hlvl : cycLevel p q k - tlW p q a = cycLevel p q (k - 1) := by
          have hstep := tlW_cycLetter_step p q hp hq (k - 1)
          have hk1 : (k - 1) + 1 = k := by ring
          rw [ha, hstep, hk1]; ring
        -- the tail of the walk is again a window walk, from the index `k-1`
        have ht : t = cycBwdList p q (k - 1) t.length := by
          apply ih (k - 1)
          · intro l hl; exact hfalse l (List.mem_cons_of_mem _ hl)
          · intro e he
            apply hwin
            have he' : e ∈ decor (tlW p q) (cycLevel p q k - tlW p q a) t := by
              rwa [hlvl]
            exact List.mem_cons_of_mem _ he'
        rw [List.length_cons, cycBwdList_succ]
        exact congrArg₂ List.cons (by rw [ha]) ht
      | true =>
        exact Bool.noConfusion (hfalse (a, true) (by simp))
  exact key L k hfalse hwin

end Work.OROneRel
