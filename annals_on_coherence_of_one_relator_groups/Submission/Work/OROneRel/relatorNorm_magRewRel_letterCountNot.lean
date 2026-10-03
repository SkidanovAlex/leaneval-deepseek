import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.relatorNorm_magRewRel_eq_of_notMem

namespace Work.OROneRel

universe u

/-- For a reduced word `L`, the norm of `mk L` is the length of `L`.  The `DecidableEq` instance is
an explicit argument so that this can be applied with the instance actually carried by `relatorNorm`
(which is the `Classical` one, not the `instDecidableEqProd` that typeclass search would pick for a
product type): `relatorNorm` unfolds to `FreeGroup.norm` at a `Classical` instance, and the two are
not syntactically the same. -/
private lemma norm_mk_of_isReduced {β : Type u} [DecidableEq β] {L : List (β × Bool)}
    (hL : FreeGroup.IsReduced L) : FreeGroup.norm (FreeGroup.mk L) = L.length := by
  rw [FreeGroup.norm, FreeGroup.toWord_mk, hL.reduce_eq]

/-- **The norm of the Magnus rewriting is the count of the letters different from the stable
letter.**  For a generator `z` and any element `w` of the free group,
`relatorNorm (magRewRel z w) = letterCountNot z w`: the Magnus rewriting `rewrite z w.toWord` deletes
exactly the `z`-letters (`rewriteAux_length`) and is reduced (`rewrite_isReduced`), and
`FreeGroup.toWord` of the rewriting is the rewriting itself.  Mind the `DecidableEq` instance
carried by `FreeGroup.toWord` (see `Submission.Work.OROneRel.nt_lt_relatorNorm` for the technique,
and `relatorNorm_magRewRel_eq_of_notMem` in the same directory for the instance dance already
worked out for the closely related statement). -/
theorem relatorNorm_magRewRel_letterCountNot {α : Type u} (z : α) (w : FreeGroup α) :
    Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel z w) = Work.OROneRel.letterCountNot z w := by
  classical
  -- The norm of `magRewRel z w` is the length of the Magnus rewriting of `toWord w`, because that
  -- rewriting is reduced.
  have hnorm : relatorNorm (magRewRel z w) = (rewrite z w.toWord).length := by
    unfold relatorNorm magRewRel
    exact @norm_mk_of_isReduced ({a : α // a ≠ z} × ℤ) (fun a b => Classical.propDecidable (a = b))
      (rewrite z w.toWord) (rewrite_isReduced z FreeGroup.isReduced_toWord)
  rw [hnorm]
  -- The length of the rewriting is exactly the number of letters different from `z`.
  unfold letterCountNot
  rw [List.countP_eq_length_filter]
  rw [show rewrite z w.toWord = rewriteAux z 0 w.toWord from rfl, rewriteAux_length]

end Work.OROneRel
