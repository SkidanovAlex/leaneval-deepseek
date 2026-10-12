import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem W1funFarIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : 2 * R ≤ ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => |Work.BoseFixR.W1fun v h ℓ z|) := by sorry

end Work.BoseBoxFock.PCFU
