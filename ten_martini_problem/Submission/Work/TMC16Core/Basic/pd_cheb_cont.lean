/-
# The "sequence continuant" and its relation to `cont`

`Work.TMC16Core.Cheb.cont l` is the continuant of a list, defined as the `(0,0)`-entry of
the ordered product of transfer matrices.  For the evaluation lemma `pd_cheb_eval` we need
the *same* continuant organised as a two-step recursion indexed by `ℕ`, which is exactly the
recursion defining `Work.TMC16Core.pd`.

This file defines that recursion (`contSeq`, whose indexing is chosen so that
`contSeq f (k+1) = cont` of the length-`k` list `[f 0, …, f (k-1)]`) and proves the
elementary list identity used to compare it with `cont`.
-/
import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_setup

namespace Work.TMC16Core.Cheb

open Matrix Polynomial

noncomputable section

/-- The continuant written as a two-step recursion on `ℕ`: `contSeq f (k+1)` is the
continuant of the length-`k` list `[f 0, …, f (k-1)]` (and `contSeq f 0 = 0` is the
"empty" convention matching `Work.TMC16Core.pd 0`). -/
def contSeq {R : Type*} [CommRing R] (f : ℕ → R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => f n * contSeq f (n + 1) - contSeq f n

/-- Concatenating two elements on the right adds one step of the continuant recursion. -/
lemma cont_append_two {R : Type*} [CommRing R] (l : List R) (c a : R) :
    cont (l ++ [c, a]) = a * cont (l ++ [c]) - cont l := by
  have h1 : (l ++ [c, a]).reverse = a :: c :: l.reverse := by
    rw [List.reverse_append]; simp
  have h2 : (c :: l.reverse).reverse = l ++ [c] := by
    rw [List.reverse_cons, List.reverse_reverse]
  rw [← cont_reverse (l ++ [c, a]), h1, cont_cons_cons, ← cont_reverse (c :: l.reverse),
    h2, cont_reverse]

/-- `contSeq` only depends on the values of the sequence. -/
lemma contSeq_congr {R : Type*} [CommRing R] {f g : ℕ → R} (h : f = g) (k : ℕ) :
    contSeq f k = contSeq g k := by rw [h]

end

end Work.TMC16Core.Cheb
