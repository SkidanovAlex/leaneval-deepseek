/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Final.Rep.H2W.Step5.s20_honesty` — de-duplication wrapper

The declarations formerly proved here (the honesty layer of the two dominating pieces of Step 5) are **re-declared** by
`Submission.Work.FTS.EllipticEst.Final.ReHome.M4_s20_honesty`, the copy that the level-`2` path uses once `H2W/slot20_bound` is routed through
`Final/slot20_bound_fts`.  The two bodies are byte-identical modulo their `import` lines, so the
names stay available, with identical statements, through the import at the end of this list.
Keeping a second copy here would be a duplicate declaration in every module whose import cone
contains both trees (`Final/Rep/*` and `Final/ReHome/*`).

The original import list is kept, so nothing that this module used to re-export transitively is
lost.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.slot20_bound
import Submission.Work.FTS.EllipticEst.H2W.slot20A
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.H2W.Step5.integrable_of_majorant
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20Aesm
import Submission.Work.FTS.EllipticEst.Final.ReHome.M4_s20_honesty

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
