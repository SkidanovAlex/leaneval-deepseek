/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The norm of the Magnus rewriting against the non-`t` letter count

For a relator `r` and a generator `t`, the Magnus rewriting `mmW t r` (the relator of the exponent
sum zero Magnus--Moldavanskii step) is obtained from `rewrite t r.toWord` by relabelling the
decorations, and that word has length `nt t r.toWord` (`rewriteAux_length`).  Since the norm of a
word is at most its length, this gives the bound used in the norm bookkeeping of the transvection
route (`Submission.Work.OROneRel.mmStepData_of_transvection`):

  `relatorNorm (mmW t r) ≤ nt t r.toWord`.

The `DecidableEq α` instance is passed explicitly here because the definitions of `mmList`, `mmWL`
and `mmW` were elaborated with `Classical.propDecidable` (see the comment in
`Submission.Work.OROneRel.relatorNorm_magRewRel_eq_nt_mine`).
-/
import Mathlib
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.ntDefs
import Submission.Work.OROneRel.rewrite_length_lt

namespace Work.OROneRel

/-- The Magnus rewriting `mmW t r` with respect to `t` is bounded in norm by the number of letters
of the reduced word of `r` that are different from `t`: it is obtained from the Magnus rewriting
`rewrite t r.toWord` (whose length is that number, `rewriteAux_length`) by relabelling the
decorations, and the norm of a word is at most its length. -/
theorem relatorNorm_mmW_le_nt {α : Type*} [DecidableEq α] (t : α) (r : FreeGroup α) :
    relatorNorm (mmW t r) ≤ nt t r.toWord := by
  classical
  have hinst : (fun a b : α => Classical.propDecidable (a = b)) = (inferInstance : DecidableEq α) :=
    Subsingleton.elim _ _
  have h1 : relatorNorm (mmW t r) ≤ (mmWL t r).length := by
    rw [relatorNorm, mmW]
    exact FreeGroup.norm_mk_le
  have h2 : (mmWL t r).length = (mmList t r).length := by rw [mmWL, List.length_map]
  have h3 : (mmList t r).length = (rewrite t r.toWord).length := by
    rw [mmList, magRew_zero_eq_rewrite, hinst]
  have h4 : (rewrite t r.toWord).length = nt t r.toWord := by
    rw [show rewrite t r.toWord = rewriteAux t 0 r.toWord from rfl, rewriteAux_length,
      nt_eq_countP, List.countP_eq_length_filter]
  omega

end Work.OROneRel
