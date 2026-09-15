import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity

namespace Commons.MeasureTheory


/-- If two functions agree almost everywhere with respect to the measure obtained by weighting
volume with the positive continuous density `x ↦ ENNReal.ofReal (F x)`, then they agree almost
everywhere with respect to volume itself. -/
theorem eventuallyEq_volume_of_ae_withDensity_ofReal_pos {d : ℕ} {F : (Fin d → ℂ) → ℝ}
    (hFc : Continuous F) (hFpos : ∀ x, 0 < F x)
    {E : Type*} {u v : (Fin d → ℂ) → E}
    (h : u =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x)))] v) :
    u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))] v := by
  refine (MeasureTheory.withDensity_ae_eq (μ := (MeasureTheory.volume :
      MeasureTheory.Measure (Fin d → ℂ))) (d := fun x => ENNReal.ofReal (F x))
    ?_ ?_).mp h
  · exact hFc.measurable.ennreal_ofReal.aemeasurable
  · filter_upwards with x
    exact (ENNReal.ofReal_pos.mpr (hFpos x)).ne'

end Commons.MeasureTheory