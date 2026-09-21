import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs

/-!
# `|S^m| = (m+1)|B^{m+1}|`

The Euclidean-space instance of `MeasureTheory.Measure.toSphere_real_apply_univ`
(`μ.toSphere.real univ = dim E * μ.real (ball 0 1)`), which is the constant identity joining the
surface measure of the unit sphere to the volume of the unit ball.  It is what makes the constant
of Prop. `workHARD1` (`|S^{d-3}| = (d-2)|B^{d-2}|`) match the `(d-2)` factor of the
integration-by-parts identity `Work.OddCurve.LowSlope.section_ibp`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory

theorem sphereArea_eq_ballVol (m : ℕ) :
    Work.OddRadon.sphereArea m = ((m : ℝ) + 1) * ballVol (m + 1) := by
  have h := MeasureTheory.Measure.toSphere_real_apply_univ
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))))
  rw [Work.OddRadon.sphereArea, ballVol]
  rw [h]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 := by
    simp [finrank_euclideanSpace_fin]
  rw [hdim]
  simp only [MeasureTheory.Measure.real]
  push_cast
  ring

end

end Work.OddCurve.LowSlope
