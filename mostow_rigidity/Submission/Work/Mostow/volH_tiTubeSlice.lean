import Mathlib
import Submission.Work.Mostow.tiDefs
import Submission.Work.Mostow.volH_fermi_prod
import Submission.Work.Mostow.fermi_inv

/-!
# `Work.Mostow.volH_tiTubeSlice`

The tube slice `tiTubeSlice j m DY ρ` is a measurable hull of the Fermi chart image of
`DY' × closedBall 0 ρ` (`DY' = toMeasurable (volH j) DY`).  Since `toMeasurable` preserves
measures, its `volH (j+m)`-volume is the product of the tangential volume `volH j DY` and the
normal-fibre measure `tubeMeasure j m (closedBall 0 ρ)`, by the rectangle identity
`Work.Mostow.volH_fermi_prod`.
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Work.Mostow

noncomputable section

theorem volH_tiTubeSlice (j m : ℕ) (DY : Set (Submission.Mostow.E j)) (ρ : ℝ) :
    Submission.Mostow.volH (j + m) (Work.Mostow.tiTubeSlice j m DY ρ)
      = Submission.Mostow.volH j DY * Submission.Mostow.tubeMeasure j m (Metric.closedBall 0 ρ) := by
  classical
  set f : Submission.Mostow.E j × Submission.Mostow.E m → Submission.Mostow.E (j + m) :=
    fun p => Submission.Mostow.fermi j m p.1 p.2 with hf
  have hslice : Work.Mostow.tiTubeSlice j m DY ρ
      = MeasureTheory.toMeasurable (Submission.Mostow.volH (j + m))
          (f '' (MeasureTheory.toMeasurable (Submission.Mostow.volH j) DY
            ×ˢ Metric.closedBall 0 ρ)) := by
    rw [hf]
    rfl
  have hball : MeasurableSet (Metric.closedBall (0 : Submission.Mostow.E m) ρ) :=
    Metric.isClosed_closedBall.measurableSet
  calc Submission.Mostow.volH (j + m) (Work.Mostow.tiTubeSlice j m DY ρ)
      = Submission.Mostow.volH (j + m)
          (f '' (MeasureTheory.toMeasurable (Submission.Mostow.volH j) DY
            ×ˢ Metric.closedBall 0 ρ)) := by
        rw [hslice, MeasureTheory.measure_toMeasurable]
    _ = Submission.Mostow.volH j
            (MeasureTheory.toMeasurable (Submission.Mostow.volH j) DY)
          * Submission.Mostow.tubeMeasure j m (Metric.closedBall 0 ρ) :=
        volH_fermi_prod j m _ _ (MeasureTheory.measurableSet_toMeasurable (Submission.Mostow.volH j) DY) hball
    _ = Submission.Mostow.volH j DY
          * Submission.Mostow.tubeMeasure j m (Metric.closedBall 0 ρ) := by
        rw [MeasureTheory.measure_toMeasurable]

end

end Work.Mostow
