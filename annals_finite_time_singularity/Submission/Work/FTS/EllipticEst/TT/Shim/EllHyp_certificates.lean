import Mathlib.Tactic.MinImports
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.DzCalc
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.TT.Shim.Fstar_smooth_of_EllHyp
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was the older variant of
-- `Submission.Work.FTS.EllipticEst.EllHyp_certificates` declaring the same names (and carrying a `sorry` that the root does not),
-- so importing both was a duplicate-declaration error.
-- The (proved) names stay available to every consumer through the import above.