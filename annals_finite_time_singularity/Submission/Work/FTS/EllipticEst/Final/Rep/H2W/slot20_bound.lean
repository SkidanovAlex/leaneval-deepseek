/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Final.Rep.H2W.slot20_bound` — de-duplication wrapper

The declarations formerly proved here (the reduction layer of the `(2,0)`-slot at level `2`) are **re-declared** by
`Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound`, the copy that the level-`2` path uses once `H2W/slot20_bound` is routed through
`Final/slot20_bound_fts`.  The two bodies are byte-identical modulo their `import` lines, so the
names stay available, with identical statements, through the import at the end of this list.
Keeping a second copy here would be a duplicate declaration in every module whose import cone
contains both trees (`Final/Rep/*` and `Final/ReHome/*`).

The original import list is kept, so nothing that this module used to re-export transitively is
lost.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Final.Rep.Mine.TopSlotTwo
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.remov.slice_step4
import Submission.Work.FTS.EllipticEst.remov.slice5_reduce
import Submission.Work.FTS.EllipticEst.remov.coerc.weak_poincare_second
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
