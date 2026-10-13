import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.weakSliceLimits
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceBounds
import Submission.Work.FTS.EllipticEst.TT.Slot11.MomentChainAux
import Submission.Work.H2W.weakSliceContinuousKit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.H2W.weakSliceContinuousKit` (same namespaces), so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.