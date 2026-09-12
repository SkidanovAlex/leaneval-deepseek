import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory MeasureTheory.Measure ENNReal Real Module Metric
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.InnerProductSpace

theorem unitBall_volume_eq_finrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : E) 1)) =
      ENNReal.toReal (MeasureTheory.volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1)) := by
  congr 1
  -- The canonical orthonormal basis of `E` gives a volume-preserving linear isometry
  -- `E ≃ₗᵢ EuclideanSpace ℝ (Fin (finrank ℝ E))`; it maps the unit ball onto the unit ball.
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  calc
    volume (Metric.closedBall (0 : E) 1)
        = volume (b.repr ⁻¹' (Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1)) := by
          rw [b.repr.preimage_closedBall]
          simp
    _ = volume (Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
          exact b.measurePreserving_repr.measure_preimage measurableSet_closedBall.nullMeasurableSet

end Commons.Analysis.InnerProductSpace
