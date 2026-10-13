import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.Elliptic.LzeroAdj_sinCos2
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.EllipticEst.remov.wsSliceLeft
import Submission.Work.FTS.EllipticEst.remov.wsMomentChain
import Submission.Work.FTS.EllipticEst.remov.wsPzBounds
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.remov.weakSliceRegular` (same namespaces), so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.