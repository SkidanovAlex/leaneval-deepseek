import Mathlib.Tactic.MinImports
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.Zsq
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.H2W.z2pzIter2Comm
import Submission.Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2`, so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.