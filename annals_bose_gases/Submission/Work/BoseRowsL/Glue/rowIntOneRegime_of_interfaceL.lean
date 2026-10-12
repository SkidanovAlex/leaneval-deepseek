import ChallengeDeps
import Submission.Work.BoseRowsL.Glue.intKernel_of_interfaceL
import Submission.Work.BoseRowsL.Glue.rowIntOneRegime_of_intKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Glue.rowIntOneRegime_of_interfaceL`

FS §11's integral row (`RowIntOneRegimeN`, i.e. FS `lem:EstimateIntegral`,
`eq:CompIntegrals-Final`) at the honest data, **assuming only the decay-free interface**
`Work.BoseRowsL.HonestInterfaceL`.

This is the decay-free analogue of `Work.BoseRowsFS.RowIntOneRegime_honest` (which is stated from
FS's two *false* pointwise decay rows `|Ŵ₁(p)|(1+‖p‖)² ≤ Cw·a v`, `|ĝ(p)|(1+‖p‖)² ≤ Cw·a v`), and
the consumer of the sibling glue module `Work.BoseRowsL.Glue.intKernel_of_interfaceL`.

* `intKernel_of_interfaceL` produces the honest `IntKernel K₀` at an effective threshold
  `ε₁ ≤ hthr.εg` and a constant `K₀ ≥ 128π` from the interface rows `bndW`, `lipW`, `tailL`,
  `fsp`, `fspKz`, `rkh`, `a16`;
* `rowIntOneRegime_of_intKernel` (this area, separate module) is the assembly step: it feeds that
  `IntKernel` into FS `lem:EstimateIntegral` in its threshold-pinned form
  (`Work.BoseB7A.estIntegralOneA_pinned`, diluteness `≤ (1/2)³²³`) and obtains the row at
  `ε₀ = min ε₁ (1/2)³²³` with the constant `2000(max K₀ 1)⁵ + 2000`.

Splitting the assembly off keeps the analytic bundle that produces the `IntKernel` out of the
import cone of the row, and makes the row available to the fleet as soon as the `IntKernel` is.

No `sorry`, no `axiom`.
-/

namespace Work.BoseRowsL.Glue

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem rowIntOneRegime_of_interfaceL {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsL.HonestInterfaceL R hthr) :
    ∃ ε₀ Kint : ℝ, 0 < ε₀ ∧ ε₀ ≤ hthr.εg ∧ 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) H.Ng' R ε₀ Kint := by
  obtain ⟨ε₁, K₀, hε₁pos, hε₁le, _hK₁, hIK⟩ :=
    intKernel_of_interfaceL (v := v) (h := h) (fc := fc) (fu := fu)
      R hR hav hv_nonneg hvrad hv_supp hthr H
  exact rowIntOneRegime_of_intKernel (v := v) (h := h) (fc := fc) (fu := fu)
    H ε₁ K₀ hε₁pos hε₁le hIK

end

end Work.BoseRowsL.Glue
