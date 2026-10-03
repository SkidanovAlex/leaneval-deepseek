import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.magnusStepDefs
import Submission.Work.OROneRel.letterCountNot_conj_cyclicReduced_le

namespace Work.ORLocInd.CohenLyndon

universe u

/-- **The Magnus rewriting of `r` at `t` is no longer than the number of non-`t` letters of `r`.**

The rewriting `mmWL t r` has the same length as the Magnus rewriting `rewrite t r.toWord`, which
deletes exactly the `t`-letters (`rewriteAux_length`); hence its length is `letterCountNot t r`.  The
norm of `magW t r = mk (mmWL t r)` is the norm of the freely reduced form of `mmWL t r`, which is at
most its length (`FreeGroup.norm_mk_le`).  No hypothesis on `r` (cyclically reduced, exponent sum
zero) is needed: this is the crude bound `≤`, not the equality of
`Work.OROneRel.relatorNorm_mmW_letterCountNot`. -/
theorem magW_relatorNorm_le_letterCountNot {α : Type u} (t : α) (r : FreeGroup α) :
    Work.OROneRel.relatorNorm (Work.ORLocInd.CohenLyndon.magW t r) ≤
      Work.OROneRel.letterCountNot t r := by
  classical
  -- The decorated rewriting `mmWL t r` has the length of the Magnus rewriting of `r`,
  -- which is exactly the number of non-`t` letters of `r`.
  have hlen : (Work.OROneRel.mmWL t r).length = Work.OROneRel.letterCountNot t r := by
    rw [Work.OROneRel.mmWL, List.length_map]
    show (Work.OROneRel.mmList t r).length = Work.OROneRel.letterCountNot t r
    rw [Work.OROneRel.mmList, Work.OROneRel.magRew_eq_rewriteAux, Work.OROneRel.rewriteAux_length]
    rw [Work.OROneRel.letterCountNot, List.countP_eq_length_filter]
  -- The norm of the class of `mmWL t r` is at most its length.
  have hnorm : Work.OROneRel.relatorNorm (Work.ORLocInd.CohenLyndon.magW t r) ≤
      (Work.OROneRel.mmWL t r).length := by
    show Work.OROneRel.relatorNorm (Work.OROneRel.mmW t r) ≤ _
    rw [Work.OROneRel.mmW]
    exact @FreeGroup.norm_mk_le (Work.OROneRel.mmBeta t r) (Work.OROneRel.mmWL t r)
      (Classical.decEq _)
  linarith

end Work.ORLocInd.CohenLyndon
