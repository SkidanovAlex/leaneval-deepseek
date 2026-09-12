import Submission.Rad.Heat
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

noncomputable section

namespace RadType
open RademacherEnfloType

/-- The open interval `(0, π/2)`. -/
def thetaSet : Set ℝ := Set.Ioc (0 : ℝ) (Real.pi / 2)

/-- Uniform probability measure on `(0, π/2)`. -/
noncomputable def thetaMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 / Real.pi)) • volume.restrict thetaSet

lemma thetaSet_measurable : MeasurableSet thetaSet := measurableSet_Ioc

@[simp] lemma thetaMeasure_univ : thetaMeasure Set.univ = 1 := by
  unfold thetaMeasure thetaSet
  rw [MeasureTheory.Measure.smul_apply]
  rw [Measure.restrict_apply (show MeasurableSet (Set.univ : Set ℝ) from MeasurableSet.univ)]
  rw [Set.univ_inter]
  rw [Real.volume_Ioc]
  change ENNReal.ofReal (2 / Real.pi) * ENNReal.ofReal (Real.pi / 2 - 0) = 1
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) / Real.pi)]
  rw [show ((2 : ℝ) / Real.pi) * (Real.pi / 2 - 0) = 1 by field_simp [Real.pi_ne_zero]; ring]
  simp

instance theta_measure_prob : IsProbabilityMeasure thetaMeasure := by
  constructor
  exact thetaMeasure_univ

end RadType
end
