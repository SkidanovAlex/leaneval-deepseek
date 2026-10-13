import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceRegular
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.TT.Slot11.MomentChainAux
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
/-!
# `H2W/Slot01W/SliceBounds` — thin re-export

The `D_z`-slot slice extractor `Work.FTS.EllipticEst.H2W.slot_slice_integrableOn` (whose earlier
home `H2W/Fstar_DzIter_le_Psi.lean` was temporarily unbuildable when this module was written) and
the whole `Work.FTS.EllipticEst.remov.SourceBound` block are now available from their canonical
homes — `H2W/Fstar_DzIter_le_Psi.lean` and `remov/SourceBound/weakSliceBounds.lean` both build
again — so this module is reduced to the corresponding import.

History: this file used to *re-declare* `endVals` and the rest of the `remov.SourceBound`
namespace, which made any module importing both it and `remov/SourceBound/weakSliceBounds`
(`FTS/EllipticEst/Prop/level2`, via `RPFresh/excess_finite`) fail with
"environment already contains `Work.FTS.EllipticEst.remov.SourceBound.endVals`".
-/
