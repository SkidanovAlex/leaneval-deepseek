import Mathlib
import Submission.Work.Serre.SPC.OneCellX
import Submission.Work.Serre.SPC.One.Main

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The integral `1`-cell step

`Work.Serre.SPC.CellStepHypOne` is proved in `Submission.Work.Serre.SPC.One.Main` as
`Work.Serre.SPC.One.cellStepHypOne_aux`; this file is the bridge that exposes it under the
requested name.

The proof assembles the four commuting squares of `Submission.Work.Serre.SPC.One.Assembly`
(compression of the complement of the centres onto the old part, excision for the open cover
`(V, Z∖P)` of `Z = attachOneCells Y ι f`, the pair map over the union `V` of the open cells and the
coproduct decomposition of `V` into the pieces) with the per-piece comparison
`Work.Serre.SPC.One.pieceChainMap_strong`, whose input is the model disc computation
`Work.Serre.SPC.One.pmMapOne_punctDisc_strong`.
-/

namespace Work.Serre.SPC

theorem oneCellStepX : Work.Serre.SPC.CellStepHypOne :=
  Work.Serre.SPC.One.cellStepHypOne_aux

end Work.Serre.SPC
