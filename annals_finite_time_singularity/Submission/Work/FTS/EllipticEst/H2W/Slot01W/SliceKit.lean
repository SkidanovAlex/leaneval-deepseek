import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.TT.Slot11.MomentChainAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excMeanSide6
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2W.weakSliceContinuousKit
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.H2W.weakSliceContinuousKit` (same namespaces), so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.