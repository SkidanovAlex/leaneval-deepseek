import Mathlib.Analysis.InnerProductSpace.PiL2
import ChallengeDeps
import Submission.Commons.Measure.Orthant.integral_orthant_eq_inv_pow
import Submission.Work.ESYRound5.Energy.pairSplit
import Submission.Work.ESYStage.neuMode_integral_zero
import Submission.Work.KinPSuperadd.fubini_abox_two
import Submission.Work.SmallBoxA0.acube_axis_ftoc
import Submission.Work.SmallBoxBridge.Kernel.volumeCosInnerZeroNull
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ESYRound8.Dict

theorem wScaled_even {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hh : ∀ z : EuclideanSpace ℝ (Fin 3), h (-z) = h z)
    (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wScaled ℓ h (-z) = Submission.BoseGases.wScaled ℓ h z := by
  unfold Submission.BoseGases.wScaled
  rw [hh z, Submission.BoseGases.convScale_symm ℓ z]

end Work.ESYRound8.Dict
