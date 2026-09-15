import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Measure.Fubini

open MeasureTheory

/-- For a finite index set, splitting a product-valued function into its two components
is measure preserving, i.e. `((∀ i, ℝ) × (∀ i, ℝ), vol × vol) ≃ᵐ ((∀ i, ℝ × ℝ), vol)`. -/
theorem measurePreserving_prodPiCurry (m : ℕ) :
    MeasureTheory.MeasurePreserving (fun p : (Fin m → ℝ) × (Fin m → ℝ) => fun i => (p.1 i, p.2 i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ × ℝ)) := by
  have h := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm
  have hf : (fun p : (Fin m → ℝ) × (Fin m → ℝ) => fun i => (p.1 i, p.2 i)) =
      ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm := by
    funext p i
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  rw [hf]
  rw [← MeasureTheory.Measure.volume_eq_prod (Fin m → ℝ) (Fin m → ℝ)]
  exact h

end Commons.Analysis.Measure.Fubini