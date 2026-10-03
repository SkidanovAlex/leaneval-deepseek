/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# `assembleT` inverts `parseT` on words starting with a non-`t` letter

`Work.OROneRel.parseT t` splits a word into the list of its non-`t` letters, each paired with the
maximal run of `t`-letters following it, and `Work.OROneRel.assembleT` glues such a decomposition
back into a word.  Leading `t`-letters are discarded by `parseT`, so `assembleT (parseT t L)` is not
`L` in general: it is `L` with all leading `t`-letters removed.

* `dropWhile_isT_of_startsNonT`: a word starting with a non-`t` letter is unaffected by
  `List.dropWhile (isT t)`.
* `assembleT_parseT_eq_dropWhile`: the precise statement, valid for *every* word `L`:
  `assembleT (parseT t L) = L.dropWhile (isT t)`.  The direction `⊇`-wise the leading `t`-run is
  the only loss, so the decomposition is faithful exactly on words starting with a non-`t` letter.
* `assembleT_parseT_of_startsNonT`: the specialisation to words with `StartsNonT t L`, which is the
  form used by the block/`parseT` calculus of `npsubstDefs`.
-/
import Mathlib
import Submission.Work.OROneRel.npsubstDefs

namespace Work.OROneRel

/-- A word starting with a non-`t` letter (in particular the empty word) is unchanged by
`List.dropWhile (isT t)`: the dropped prefix is empty. -/
theorem dropWhile_isT_of_startsNonT {β : Type*} [DecidableEq β] {t : β} {L : List (β × Bool)}
    (h : Work.OROneRel.StartsNonT t L) : L.dropWhile (Work.OROneRel.isT t) = L := by
  cases L with
  | nil => rfl
  | cons c rest =>
    exact List.dropWhile_cons_of_neg (p := isT t) (a := c) (l := rest)
      (by simp [isT, h c rest rfl])

/-- `assembleT` inverts `parseT` up to the leading run of `t`-letters: for an arbitrary word `L`,
`assembleT (parseT t L) = L.dropWhile (isT t)`.  Proved by strong induction on the length, since the
recursion of `parseT` passes to `L.dropWhile (isT t)` after a non-`t` letter, which is not a
subterm. -/
theorem assembleT_parseT_eq_dropWhile {β : Type*} [DecidableEq β] (t : β) (L : List (β × Bool)) :
    Work.OROneRel.assembleT (Work.OROneRel.parseT t L) = L.dropWhile (Work.OROneRel.isT t) := by
  have key : ∀ n, ∀ M : List (β × Bool), M.length = n →
      Work.OROneRel.assembleT (Work.OROneRel.parseT t M) = M.dropWhile (Work.OROneRel.isT t) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih M hM
    cases M with
    | nil => simp [Work.OROneRel.assembleT]
    | cons c rest =>
      by_cases hc : c.1 = t
      · -- a leading `t`-letter: both sides drop it and we recurse on `rest`
        rw [Work.OROneRel.parseT_cons_of_eq hc,
          List.dropWhile_cons_of_pos (p := Work.OROneRel.isT t) (a := c) (l := rest)
            (by simp [Work.OROneRel.isT, hc])]
        exact ih rest.length (by simp at hM; omega) rest rfl
      · -- a non-`t` letter: it is kept, its `t`-run is taken out by `takeWhile`, and the rest
        -- (which starts non-`t`) is handled recursively
        rw [Work.OROneRel.parseT_cons_of_ne hc, Work.OROneRel.assembleT_cons,
          List.dropWhile_cons_of_neg (p := Work.OROneRel.isT t) (a := c) (l := rest)
            (by simp [Work.OROneRel.isT, hc])]
        have hW : Work.OROneRel.StartsNonT t (rest.dropWhile (Work.OROneRel.isT t)) :=
          Work.OROneRel.startsNonT_dropWhile t rest
        have hlen : (rest.dropWhile (Work.OROneRel.isT t)).length < n := by
          have hle := List.length_dropWhile_le (Work.OROneRel.isT t) rest
          simp at hM
          omega
        rw [ih _ hlen (rest.dropWhile (Work.OROneRel.isT t)) rfl,
          dropWhile_isT_of_startsNonT hW, List.takeWhile_append_dropWhile]
  exact key L.length L rfl

theorem assembleT_parseT_of_startsNonT {β : Type*} [DecidableEq β] {t : β} {L : List (β × Bool)}
    (h : Work.OROneRel.StartsNonT t L) :
    Work.OROneRel.assembleT (Work.OROneRel.parseT t L) = L := by
  rw [assembleT_parseT_eq_dropWhile t L, dropWhile_isT_of_startsNonT h]

end Work.OROneRel
