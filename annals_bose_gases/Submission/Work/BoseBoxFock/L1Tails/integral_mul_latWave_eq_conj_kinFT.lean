import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.latDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

theorem integral_mul_latWave_eq_conj_kinFT (W : EuclideanSpace ℝ (Fin 3) → ℝ) (κ : EuclideanSpace ℝ (Fin 3)) :
    ∫ x, (W x : ℂ) * Work.BoseBoxFock.L1Tails.latWave κ x
      = (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun y => (W y : ℂ)) κ) := by
  rw [show Submission.BoseGases.kinFT (fun y => (W y : ℂ)) κ
        = ∫ y, Complex.exp (-(Complex.I * ((inner ℝ κ y : ℝ) : ℂ))) * (W y : ℂ) from rfl]
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [Work.BoseBoxFock.L1Tails.latWave, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp [map_mul, map_neg]
  ring

end Work.BoseBoxFock.L1Tails
