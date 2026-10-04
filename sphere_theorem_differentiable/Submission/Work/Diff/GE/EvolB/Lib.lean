import Submission.Work.Diff.GE.EvolB.Defs
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.MovingFrame.tendsto_multilinear_apply
import Submission.Work.Diff.GE.MovingFrame.multilinear_eventually_bounded
import Submission.Work.Diff.GE.MovingFrame.isONFrame_at_of_eventually
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed
import Submission.Work.Diff.GE.EvolA.rmReact_norm_le
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.onFrameONfield
import Submission.Work.Diff.GE.frameMotion_cancel_cov2Rm
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.cov2Rm_ricci_defs
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.rot_contract
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.FlowCont.rmNormSq_continuousWithinAt
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.GE.EvolB` : the import gate for the `EvolB` development

This module collects the **sorry-free** modules of the workspace that the `EvolB` development of the
fixed-vector `∇Rm` evolution is built from, so that delegated statements (which are elaborated in a
file containing only the `depends_on` imports) can mention all the needed vocabulary.

Declarations that are clean here (`#print axioms` gives only `propext, Classical.choice,
Quot.sound`): `Work.Diff.GE.NablaRm`, `ReactionDefs`, `ExtTensor`, `lapRmAt_trace`,
`onFrameONfield`, `frameMotion_cancel_cov2Rm`, `kato_cov3RmExt_field`, `cov2Rm_ricci_defs`,
`EvolA.rmP_evol_fixed`, `EvolA.rmReact_norm_le`, `reaction_map_defs`,
`FlowCont.rmNormSq_continuousWithinAt`, and the `Ext`-pattern tools of `ExtTensor`.

**Caution.**  Some modules in the closure of the imports below *do* contain declarations with a
`sorry` (they are imported transitively, not for their own sake); a proof written here must not use
them.  In particular do **not** use `Work.Diff.GE.extDD_antisymm`,
`Work.Diff.GE.cov3Rm_swap`, `Work.Diff.GE.cov3Rm_ricci`, `Work.Diff.GE.covLapRmAt_eq_sum_cov3Rm`,
`Work.Diff.GE.kato_geodesic_frame`, `Work.Diff.GE.covReactionFormAt_le` or
`Work.Diff.GE.covReactionFormAt_le_A` — check with `#print axioms` at the end.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

end Work.Diff.GE.EvolB
