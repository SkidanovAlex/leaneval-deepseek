import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.mmStepData_of_expsum_zero

namespace Work.OROneRel

universe u

/-- **The norm of the Magnus rewriting is the count of the letters different from the stable
letter.**  For a cyclically reduced relator `R` in which the exponent sum of `z` vanishes,
`relatorNorm (mmW z R) = letterCountNot z R`: the word `mmWL z R` of the rewritten relator is the
Magnus rewriting `rewrite z R.toWord` of the reduced word of `R` (transported into the decorated
alphabet `mmBeta z R`, which is the identity on the letters that occur), it is reduced by
`mmWL_isReduced`, and the rewriting drops exactly the `z`-letters (`rewriteAux_length`).  Mind the
`DecidableEq` instance carried by `FreeGroup.toWord` (see
`Submission.Work.OROneRel.nt_lt_relatorNorm` for the technique). -/
theorem relatorNorm_mmW_letterCountNot {α : Type u} (z : α) (R : FreeGroup α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R) (h : Work.OROneRel.eps z R = 0) :
    Work.OROneRel.relatorNorm (Work.OROneRel.mmW z R) = Work.OROneRel.letterCountNot z R := by
  classical
  -- The word of `mmW z R` is the Magnus rewriting `mmWL z R`, which is reduced.
  have hred : FreeGroup.IsReduced (Work.OROneRel.mmWL z R) :=
    Work.OROneRel.mmWL_isReduced z R hcyc h
  have hnorm : Work.OROneRel.relatorNorm (Work.OROneRel.mmW z R) =
      (Work.OROneRel.mmWL z R).length := by
    rw [Work.OROneRel.relatorNorm, Work.OROneRel.mmW, FreeGroup.norm, FreeGroup.toWord_mk,
      hred.reduce_eq]
  rw [hnorm]
  -- `mmWL z R` is `mmList z R` with the decorations transported into `mmBeta z R`, so its length
  -- is that of the Magnus rewriting `rewrite z R.toWord` of the reduced word of `R`.
  rw [show Work.OROneRel.mmWL z R = (Work.OROneRel.mmList z R).map
      (fun p => (Work.OROneRel.mmBetaOf z R p.1, p.2)) from rfl]
  rw [List.length_map]
  rw [show Work.OROneRel.mmList z R = Work.OROneRel.magRew z 0 (FreeGroup.toWord R) from rfl]
  rw [Work.OROneRel.magRew_zero_eq_rewrite]
  rw [show Work.OROneRel.rewrite z (FreeGroup.toWord R) =
      Work.OROneRel.rewriteAux z 0 (FreeGroup.toWord R) from rfl]
  -- The rewriting drops exactly the `z`-letters, and `letterCountNot` counts them.
  rw [Work.OROneRel.rewriteAux_length]
  rw [show Work.OROneRel.letterCountNot z R =
      (FreeGroup.toWord R).countP (fun p => p.1 ≠ z) from rfl]
  rw [List.countP_eq_length_filter]

end Work.OROneRel
