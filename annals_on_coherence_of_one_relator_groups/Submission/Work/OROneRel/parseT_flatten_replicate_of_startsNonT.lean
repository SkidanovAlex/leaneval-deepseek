/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The run decomposition of a periodic word

`Work.OROneRel.parseT t` splits a word over `β × Bool` into the list of its non-`t` letters, each
paired with the maximal run of `t`-letters that follows it (`Work.OROneRel.npsubstDefs`).  It is
faithful exactly on words that start with a non-`t` letter (`Work.OROneRel.StartsNonT`).

On such words `parseT t` is compatible with concatenation on the right
(`Work.OROneRel.parseT_append_of_startsNonT`): if the appended word starts with a non-`t` letter,
the trailing `t`-run of the first word cannot absorb anything.  Iterating this, the run
decomposition of the concatenation of `k` copies of `A` is the concatenation of the `k` copies of
the run decomposition of `A`:

  `parseT t (List.replicate k A).flatten = (List.replicate k (parseT t A)).flatten`.
-/
import Mathlib
import Submission.Work.OROneRel.npsubstDefs
import Submission.Work.OROneRel.parseT_append_of_startsNonT

namespace Work.OROneRel

theorem parseT_flatten_replicate_of_startsNonT {β : Type*} [DecidableEq β] {t : β} {A : List (β × Bool)}
    (hA : Work.OROneRel.StartsNonT t A) (k : ℕ) :
    Work.OROneRel.parseT t (List.replicate k A).flatten =
      (List.replicate k (Work.OROneRel.parseT t A)).flatten := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- `flatten (replicate (k+1) A) = flatten (replicate k A) ++ A`: the last copy is appended on
    -- the right, so compatibility of `parseT` with concatenation applies to it.
    have hstep : (List.replicate (Nat.succ k) A).flatten = (List.replicate k A).flatten ++ A := by
      rw [List.replicate_succ', List.flatten_append]
      simp
    have hsplit : Work.OROneRel.parseT t ((List.replicate k A).flatten ++ A) =
        Work.OROneRel.parseT t (List.replicate k A).flatten ++ Work.OROneRel.parseT t A :=
      Work.OROneRel.parseT_append_of_startsNonT (t := t) (A := (List.replicate k A).flatten)
        (B := A) hA
    have hfin : (List.replicate k (Work.OROneRel.parseT t A)).flatten ++
          Work.OROneRel.parseT t A =
        (List.replicate (Nat.succ k) (Work.OROneRel.parseT t A)).flatten := by
      rw [List.replicate_succ', List.flatten_append]
      simp
    rw [hstep, hsplit, ih, hfin]

end Work.OROneRel
