import Mathlib
import Submission.Work.OROneRel.liveDecorDefs

/-!
# The levels of the letters of a decorated word

The decorated word `decor c v w` of `Submission/Work/OROneRel/MagnusGenDefs.lean` is a walk on the
levels `ℤ`: the `j`-th decorated letter `p` runs from the level `coverSrc c p` to the level
`coverTgt c p`.  Reading the letters of `w` from the left at running weight `v` gives the levels
`v + lsig c (w.take j)` (`j = 0, …, w.length`), and the `j`-th letter of the walk runs between the
`j`-th and the `(j+1)`-st of them.  This file records exactly that:

* `decorGetElemCover` -- the source level of the `j`-th decorated letter is `v + lsig c (w.take j)`
  and its target level is `v + lsig c (w.take (j+1))`.

The two halves are proved separately (`coverSrc_decor_getElem`, `coverTgt_decor_getElem`) by
induction on `w`, with

* `decor_cons_l` -- the first letter of `decor c v (p :: t)` is decorated at level `v`, the rest is
  the decoration of `t` at level `v + linc c p`;
* `lsig_cons_l` -- `lsig` of a cons splits off `linc` of the head;
* `coverSrc_head_l` / `coverTgt_head_l` -- the levels of the letter decorating `p` at level `v`.
-/

namespace Work.OROneRel

/-- The weight of a word is the sum of the weights of its letters (stated at the head of the
list). -/
theorem lsig_cons_l {α : Type*} (c : α → ℤ) (p : α × Bool) (L : List (α × Bool)) :
    lsig c (p :: L) = linc c p + lsig c L := by
  obtain ⟨a, b⟩ := p
  cases b <;> simp [lsig, linc, List.sum_cons]

/-- **The decoration of a cons.**  The head letter is decorated at the level `v`, and the tail is
decorated at the running level `v + linc c p`. -/
theorem decor_cons_l {α : Type*} (c : α → ℤ) (v : ℤ) (p : α × Bool) (t : List (α × Bool)) :
    decor c v (p :: t) =
      ((p.1, if p.2 then v else v - c p.1), p.2) :: decor c (v + linc c p) t := by
  obtain ⟨a, b⟩ := p
  cases b
  · rfl
  · rfl

/-- The source level of the letter decorating `p` read at level `v`. -/
theorem coverSrc_head_l {α : Type*} (c : α → ℤ) (v : ℤ) (p : α × Bool) :
    coverSrc c ((p.1, if p.2 then v else v - c p.1), p.2) = v := by
  obtain ⟨a, b⟩ := p
  cases b
  · simp only [Bool.false_eq_true, if_false, coverSrc]; ring
  · simp only [if_true, coverSrc]

/-- The target level of the letter decorating `p` read at level `v`. -/
theorem coverTgt_head_l {α : Type*} (c : α → ℤ) (v : ℤ) (p : α × Bool) :
    coverTgt c ((p.1, if p.2 then v else v - c p.1), p.2) = v + linc c p := by
  obtain ⟨a, b⟩ := p
  cases b
  · simp only [Bool.false_eq_true, if_false, coverTgt, linc]; ring
  · simp only [if_true, coverTgt, linc]

/-- **The source levels of the decorated letters.**  The `j`-th decorated letter starts at the
running level `v + lsig c (w.take j)`. -/
theorem coverSrc_decor_getElem {α : Type*} (c : α → ℤ) (v : ℤ) (w : List (α × Bool)) (j : ℕ)
    (hj : j < (decor c v w).length) :
    coverSrc c ((decor c v w)[j]'hj) = v + lsig c (w.take j) := by
  induction w generalizing v j with
  | nil => simp [decor] at hj
  | cons p t ih =>
    simp only [decor_cons_l, List.length_cons] at hj ⊢
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_zero, lsig, List.map_nil, List.sum_nil,
        add_zero, coverSrc_head_l]
    | succ k =>
      have hk : k < (decor c (v + linc c p) t).length := by omega
      rw [List.getElem_cons_succ, List.take_succ_cons, lsig_cons_l, ih (v + linc c p) k hk]
      ring

/-- **The target levels of the decorated letters.**  The `j`-th decorated letter arrives at the
running level `v + lsig c (w.take (j+1))`. -/
theorem coverTgt_decor_getElem {α : Type*} (c : α → ℤ) (v : ℤ) (w : List (α × Bool)) (j : ℕ)
    (hj : j < (decor c v w).length) :
    coverTgt c ((decor c v w)[j]'hj) = v + lsig c (w.take (j + 1)) := by
  induction w generalizing v j with
  | nil => simp [decor] at hj
  | cons p t ih =>
    simp only [decor_cons_l, List.length_cons] at hj ⊢
    cases j with
    | zero =>
      rw [List.getElem_cons_zero, List.take_succ_cons, List.take_zero, lsig_cons_l, lsig,
        List.map_nil, List.sum_nil, add_zero]
      exact coverTgt_head_l c v p
    | succ k =>
      have hk : k < (decor c (v + linc c p) t).length := by omega
      rw [List.getElem_cons_succ, List.take_succ_cons, lsig_cons_l, ih (v + linc c p) k hk]
      ring

theorem decorGetElemCover {α : Type*} (c : α → ℤ) (v : ℤ) (w : List (α × Bool)) (j : ℕ)
    (hj : j < w.length) :
    Work.OROneRel.coverSrc c
        ((Work.OROneRel.decor c v w)[j]'(by rw [Work.OROneRel.decor_length]; exact hj)) =
      v + Work.OROneRel.lsig c (w.take j) ∧
    Work.OROneRel.coverTgt c
        ((Work.OROneRel.decor c v w)[j]'(by rw [Work.OROneRel.decor_length]; exact hj)) =
      v + Work.OROneRel.lsig c (w.take (j + 1)) := by
  constructor
  · exact coverSrc_decor_getElem c v w j (by rw [decor_length]; exact hj)
  · exact coverTgt_decor_getElem c v w j (by rw [decor_length]; exact hj)

end Work.OROneRel
