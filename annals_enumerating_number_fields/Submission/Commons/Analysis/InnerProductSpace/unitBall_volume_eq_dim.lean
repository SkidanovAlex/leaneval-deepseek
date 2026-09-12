import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_eq_finrank

open MeasureTheory MeasureTheory.Measure ENNReal Real Module Metric
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.InnerProductSpace

theorem unitBall_volume_eq_dim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {r : ℕ}
    (hfin : Module.finrank ℝ E = r) :
    ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : E) 1)) =
      ENNReal.toReal (MeasureTheory.volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin r)) 1)) := by
  subst hfin
  exact unitBall_volume_eq_finrank (E := E)

end Commons.Analysis.InnerProductSpace
