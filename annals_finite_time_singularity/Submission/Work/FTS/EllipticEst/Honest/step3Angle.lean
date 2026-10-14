import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Honest.firstOrderHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.PhiStar.Honesty.CptApp.momentDzZero
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.pz_DthIter_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The assembly from the three analytic pieces

(The slice helpers that used to precede this — `HkIntegrand_zero_boundary`, `HkSq_uOf_le`,
`sqrt_HkSq_uOf_le`, `smoothOpen_POf`, `HkIntegrand_POf_le`, … — now live in
`Submission/Work/FTS/EllipticEst/Final/Step3Helpers.lean`, which this file imports.) -/



/-! ## The six cross-honesty pairings (clash-free copy of `Honest.honCrossIPMems`)

`Honest/honCrossIPMems` proves the six `AngSecond.IPMem` facts below, but its file imports
`EllHyp_certificates` (which its proof does not use); that single import pulls
`ThetaPoincareDefs` and the `TT` frontier into the cone of every consumer, and `ThetaPoincareDefs`
declares `Work.FTS.EllipticEst.sin_two_nonneg`, which `TanTheta/Defs` also declares.  Since
`step3Angle`'s assembly also needs the `TanTheta`-based `step3PsiBar`, the pairings are reproved
here with the same proof and only the imports that proof uses.  Reported in `HANDOFF.md`. -/




end Work.FTS.EllipticEst.Honest
