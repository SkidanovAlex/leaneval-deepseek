import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAsymB
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.ZDecay_of_decay_bounds
import Submission.Work.Stability.CutFactorFderivZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Positivity of the first radial slot -/


/-! ## `ℋ^k`-membership of a product -/


/-! ## The two slot-integrability instantiations for the ansatz -/





/-! ## The boundary traces -/



/-! ## Membership in `RegQ` -/




end Work.FTS.CoercivityFix.Assembly
