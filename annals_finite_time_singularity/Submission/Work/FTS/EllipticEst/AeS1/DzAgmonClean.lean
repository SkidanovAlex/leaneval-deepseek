import Mathlib.Tactic.MinImports
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AeS1.AgmonSliceBlocks
import Submission.Work.FTS.EllipticEst.AeS1.ZsqMixedOpen
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.EllipticEst.DzAmgm.Defs
import Submission.Work.FTS.EllipticEst.AeS1.DzScratch
import Submission.Work.FTS.EllipticEst.DzCalc
import Submission.Work.FTS.EllipticEst.Blocks.TermAgmon
import Submission.Work.FTS.EllipticEst.Blocks.SliceZDeriv_finite
import Submission.Work.FTS.EllipticEst.Blocks.DzAgmonDefs
import Submission.Work.FTS.EllipticEst.Blocks.AgmonIBP
import Submission.Work.FTS.EllipticEst.Blocks.AgmonDerivVanishing
import Submission.Work.FTS.EllipticEst.Blocks.AgmonArith
import Submission.Work.FTS.EllipticEst.Blocks.AgmonSmallness
import Submission.Work.FTS.EllipticEst.Blocks.logChiFamily
import Submission.Work.FTS.EllipticEst.TT.logCutDefs
import Submission.Work.Stability.Cutoff
import Submission.Work.EllipticEst.logChi_second_deriv_le
import Submission.Work.EllipticEst.agmon_cutoff_estimate
import Submission.Work.EllipticEst.logChi_iSup_lintegral
import Submission.Work.Blocks.DzV_amgm_clean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.Blocks.DzV_amgm_clean` (same namespaces), so importing both was a duplicate-declaration
-- error.  The names stay available to every consumer of this module through the import
-- above.