/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The norm of the Magnus rewriting when `t` does not occur in the relator

`magRewRel t v = mk (rewrite t v.toWord)` deletes the letters equal to `t` from the reduced word of
`v` and decorates the remaining letters by the running exponent sum of `t`.  Consequently

* the Magnus rewriting of a reduced word is again reduced (`rewrite_isReduced`), so the norm of
  `magRewRel t (mk W)` is just the length of `rewrite t W`;
* the length of `rewrite t W` is the number of letters of `W` different from `t`
  (`rewriteAux_length`).

If `t` is not a letter of `v`, no letter is deleted, so that length is `W.length = norm v`.  This is
the required statement: `relatorNorm` is invariant under Magnus rewriting with respect to a letter
that does not occur in the relator.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.rewrite_length_lt

namespace Work.OROneRel

universe u

/-- For a *reduced* word `W`, the norm of `magRewRel t (mk W)` is the length of the Magnus rewriting
`rewrite t W`: the rewriting of a reduced word is reduced, so it computes the norm of its own class.

The `DecidableEq` instance is written out explicitly because `relatorNorm` unfolds to
`FreeGroup.norm` using `Classical.propDecidable`; writing it by hand keeps the unfolding on the
nose. -/
private lemma relatorNorm_magRewRel_mk_of_isReduced {α : Type u} (t : α) {W : List (α × Bool)}
    (hW : FreeGroup.IsReduced W) :
    relatorNorm (magRewRel t (FreeGroup.mk W)) = (rewrite t W).length := by
  classical
  unfold relatorNorm magRewRel
  have h1 : @FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b))
      (FreeGroup.mk W) = W := by
    rw [FreeGroup.toWord_mk, hW.reduce_eq]
  rw [h1]
  show (@FreeGroup.reduce ({a : α // a ≠ t} × ℤ) (fun a b => Classical.propDecidable (a = b))
      (rewrite t W)).length = (rewrite t W).length
  exact congrArg List.length
    (@FreeGroup.IsReduced.reduce_eq ({a : α // a ≠ t} × ℤ) (rewrite t W)
      (fun a b => Classical.propDecidable (a = b)) (rewrite_isReduced t hW))

theorem relatorNorm_magRewRel_eq_of_notMem {α : Type u} (t : α) {v : FreeGroup α}
    (h : t ∉ Work.OROneRel.relatorLetters v) :
    Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t v) = Work.OROneRel.relatorNorm v := by
  classical
  -- `t` is not a letter of the reduced word of `v`
  have hL : ∀ p ∈ v.toWord, p.1 ≠ t := by
    rintro ⟨a, b⟩ hp hpt
    exact h ⟨b, by rw [← hpt]; exact hp⟩
  -- so the Magnus rewriting deletes nothing
  have hmem : ∀ p ∈ v.toWord, (decide (p.1 ≠ t)) = true := by
    intro p hp
    simp [hL p hp]
  have hfilt : (v.toWord).filter (fun p => decide (p.1 ≠ t)) = v.toWord :=
    List.filter_eq_self.mpr hmem
  have hnorm : relatorNorm v = v.toWord.length := rfl
  rw [hnorm]
  conv_lhs => rw [← FreeGroup.mk_toWord (x := v)]
  rw [relatorNorm_magRewRel_mk_of_isReduced t FreeGroup.isReduced_toWord]
  rw [show Work.OROneRel.rewrite t v.toWord = Work.OROneRel.rewriteAux t 0 v.toWord from rfl,
    rewriteAux_length, hfilt]

end Work.OROneRel
