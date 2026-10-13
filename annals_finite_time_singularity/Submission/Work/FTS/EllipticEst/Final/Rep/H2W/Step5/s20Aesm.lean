/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Final.Rep.H2W.Step5.s20Aesm` — de-duplication wrapper

The declarations formerly proved here (the a.e.-strong-measurability layer of the Step-5 source) are **re-declared** by
`Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_Step5_s20Aesm`, the copy that the level-`2` path uses once `H2W/slot20_bound` is routed through
`Final/slot20_bound_fts`.  The two bodies are byte-identical modulo their `import` lines, so the
names stay available, with identical statements, through the import at the end of this list.
Keeping a second copy here would be a duplicate declaration in every module whose import cone
contains both trees (`Final/Rep/*` and `Final/ReHome/*`).

The original import list is kept, so nothing that this module used to re-export transitively is
lost.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.slot20_bound
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_Step5_s20Aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
