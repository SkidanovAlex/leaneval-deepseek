import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.Z3Clean
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.CoercivityStep.Step
import Submission.Work.FTS.CoercivityStep.Step.Coercive
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Nonnegativity of the energies -/






/-! ## The two elementary `IntegrableOn`/`wip` lemmas of `zQuad`

`Submission/Work/Coercivity/zQuad.lean` proves the additivity lemmas for `wip` that the
`D_z`-estimate uses, but it also declares a `wip_congr_ae` whose name clashes with the
one of `thetaDerivative.lean`; the two modules can therefore not be imported together.
The two lemmas needed here are reproduced under fresh names (with `wip_add_left` of
`wip_Aop_ge.lean` in place of `zQuad`'s `wip_add`). -/



/-! ## The `D_z`-coercivity estimate -/


/-! ## The numerical bookkeeping -/


/-! ## The base case of the `ℋ¹` coercivity -/


end Work.Coercivity
