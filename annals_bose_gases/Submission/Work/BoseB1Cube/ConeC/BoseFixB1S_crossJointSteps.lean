import ChallengeDeps
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxMuSumAgree
import Submission.Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1
import Submission.Work.BoseFixB1.boxQ1CrossSqrtB1
import Submission.Work.BoseFixB1S.PQIdentAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases Work.UBBInputs8

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **§14 step 0**: the fibre mass of the sliding-box kernel `w₁` is nonnegative — the
`hM1nn` hypothesis of `boxCrossJoint` is a *theorem* under the target's own hypotheses. -/
theorem boxM1_nonneg_wSmall {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u : E3) :
    0 ≤ Work.BoseFixB1S.boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u) :=
  Work.BoseFixB1.boxM1_nonneg (Work.BoseFixB1.q1cw1_w1Fibre_nonneg hv_supp hR0 hv hvrad h u)

end Work.BoseFixB1S
