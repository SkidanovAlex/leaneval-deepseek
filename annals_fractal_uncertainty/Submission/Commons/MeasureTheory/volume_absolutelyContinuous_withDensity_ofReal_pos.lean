import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity

namespace Commons.MeasureTheory

open _root_.MeasureTheory

theorem volume_absolutelyContinuous_withDensity_ofReal_pos {d : ℕ} {F : (Fin d → ℂ) → ℝ}
    (hFc : Continuous F) (hFpos : ∀ x, 0 < F x) :
    MeasureTheory.Measure.AbsolutelyContinuous
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x))) := by
  intro s hs
  rw [MeasureTheory.withDensity_apply' _ s] at hs
  rw [lintegral_eq_zero_iff (f := fun x : Fin d → ℂ => ENNReal.ofReal (F x))
        (ENNReal.continuous_ofReal.measurable.comp hFc.measurable)] at hs
  have h' : ∀ᵐ x ∂((volume : Measure (Fin d → ℂ)).restrict s),
      (fun x => ENNReal.ofReal (F x)) x = 0 := hs
  rw [ae_iff] at h'
  have hset : {x : Fin d → ℂ | ¬ ((fun x => ENNReal.ofReal (F x)) x = 0)} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (hFpos x)).ne'
  rw [hset, Measure.restrict_apply_univ] at h'
  exact h'

end Commons.MeasureTheory