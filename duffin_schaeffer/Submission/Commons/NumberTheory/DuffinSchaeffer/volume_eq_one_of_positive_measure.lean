import Mathlib.NumberTheory.WellApproximable

open MeasureTheory Filter Set Metric

namespace Commons.NumberTheory.DuffinSchaeffer

/-- Gallagher's ergodic theorem gives that the set of well-approximable numbers in the circle is
either almost empty or almost full.  Combined with the hypothesis that it has positive measure,
we conclude that it has full measure. -/
theorem volume_eq_one_of_positive_measure (δ : ℕ → ℝ)
    (hδt : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hpos : 0 < MeasureTheory.volume (addWellApproximable UnitAddCircle δ)) :
    MeasureTheory.volume (addWellApproximable UnitAddCircle δ) = 1 := by
  let E : Set UnitAddCircle := addWellApproximable UnitAddCircle δ
  have hE : addWellApproximable UnitAddCircle δ = E := rfl
  rw [hE] at hpos ⊢
  rcases (AddCircle.addWellApproximable_ae_empty_or_univ (T := (1 : ℝ)) δ hδt) with h | h
  · have h0 : volume E = 0 := by
      have h0' := (MeasureTheory.ae_iff (μ := volume) (p := fun x : UnitAddCircle => x ∉ E)).mp h
      simpa using h0'
    simp [h0] at hpos
  · have hEc : volume Eᶜ = 0 := by
      have hEc' := (MeasureTheory.ae_iff (μ := volume) (p := fun x : UnitAddCircle => x ∈ E)).mp h
      rw [compl_def E]
      exact hEc'
    have hu : volume (univ : Set UnitAddCircle) = 1 := by
      simp [AddCircle.measure_univ]
    have hle : volume (univ : Set UnitAddCircle) ≤ volume E := by
      calc
        volume (univ : Set UnitAddCircle) = volume (E ∪ Eᶜ) := by
          congr 1
          ext x
          by_cases hx : x ∈ E <;> simp
        _ ≤ volume E + volume Eᶜ := measure_union_le E Eᶜ
        _ = volume E := by simp [hEc]
    have hge : volume E ≤ volume (univ : Set UnitAddCircle) := measure_mono (subset_univ E)
    have hE1 : volume E = 1 := by
      rw [← hu]
      exact le_antisymm hge hle
    exact hE1

end Commons.NumberTheory.DuffinSchaeffer
