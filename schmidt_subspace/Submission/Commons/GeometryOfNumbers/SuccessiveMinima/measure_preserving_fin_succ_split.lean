import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open MeasureTheory Set
open scoped Pointwise

/-- **Splitting off the last coordinate of `ℝ^{j+1}` as a measure-preserving equivalence.**

There is a measurable equivalence `(Fin (j+1) → ℝ) ≃ᵐ (Fin j → ℝ) × ℝ` which is the identity
on the first `j` coordinates and the last coordinate on the second factor, and which preserves
the Lebesgue measure.

Suggested proof: `MeasurableEquiv.sumPiEquivProdPi` together with `Fin.sumFinEquiv` (or
`finSumFinEquiv`) reindexing `Fin (j+1)` as `Fin j ⊕ Fin 1`, plus
`MeasureTheory.volume_measurePreserving_sumPiEquivProdPi`,
`MeasureTheory.volume_measurePreserving_piCongrLeft` and the identification
`(Fin 1 → ℝ) ≃ᵐ ℝ`. -/
theorem measure_preserving_fin_succ_split (j : ℕ) :
    ∃ e : (Fin (j+1) → ℝ) ≃ᵐ ((Fin j → ℝ) × ℝ),
      MeasurePreserving e volume volume ∧
      (∀ x : Fin (j+1) → ℝ, (e x).2 = x (Fin.last j)) ∧
      (∀ x : Fin (j+1) → ℝ, (e x).1 = fun k : Fin j => x (Fin.castSucc k)) := by
  refine ⟨(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j+1) => ℝ) (Fin.last j)).trans
    MeasurableEquiv.prodComm, ?_, ?_, ?_⟩
  · exact (volume_preserving_piFinSuccAbove (fun _ : Fin (j+1) => ℝ) (Fin.last j)).trans
      (MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume))
  · intro x; rfl
  · intro x; ext k
    simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm, Fin.init]

end Commons.GeometryOfNumbers.SuccessiveMinima