/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The reduced word of a product of two powers of distinct generators

`wordOf` is `FreeGroup.toWord` at `Classical.decEq` (see `wordOfDefs`).  For two distinct
generators `a ≠ b` the word

`FreeGroup.of a ^ p * FreeGroup.of b ^ q`

is *already* reduced: the reduced word of `of a ^ p` is the block of `p` copies of the letter
`(a, true)` (`FreeGroup.toWord_of_pow`), that of `of b ^ q` is the block of `q` copies of
`(b, true)`, and since the last letter of the first block and the first letter of the second block
have different generators, nothing cancels at the junction.  Hence the reduced word of the product
is the plain concatenation of the two blocks.
-/

import Mathlib
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

/-- The concatenation of `p` copies of the letter `(a, true)` and `q` copies of the letter
`(b, true)` is reduced when `a ≠ b`: the only possible cancellation is at the junction, where the
two letters have distinct generators. -/
private theorem isReduced_replicate_pair {α : Type*} (a b : α) (hab : a ≠ b) (p q : ℕ) :
    FreeGroup.IsReduced
      (List.replicate p ((a, true) : α × Bool) ++ List.replicate q ((b, true) : α × Bool)) := by
  rw [FreeGroup.IsReduced]
  refine List.IsChain.append (List.isChain_replicate_of_rel p (by intro _; rfl))
    (List.isChain_replicate_of_rel q (by intro _; rfl)) ?_
  intro x hx y hy
  rw [List.getLast?_replicate] at hx
  rw [List.head?_replicate] at hy
  split_ifs at hx hy with hp hq
  · simp at hx
  · simp at hx
  · simp at hy
  · simp only [Option.mem_some_iff] at hx hy
    rw [← hx, ← hy]
    intro h
    exact absurd h hab

theorem wordOf_of_pow_mul_of_pow {α : Type*} (a b : α) (hab : a ≠ b) (p q : ℕ) :
    Work.OROneRel.wordOf (FreeGroup.of a ^ p * FreeGroup.of b ^ q)
      = List.replicate p (a, true) ++ List.replicate q (b, true) := by
  classical
  have hred := isReduced_replicate_pair a b hab p q
  show FreeGroup.toWord (FreeGroup.of a ^ p * FreeGroup.of b ^ q) = _
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of_pow, FreeGroup.toWord_of_pow]
  exact FreeGroup.IsReduced.reduce_eq hred

end Work.OROneRel
