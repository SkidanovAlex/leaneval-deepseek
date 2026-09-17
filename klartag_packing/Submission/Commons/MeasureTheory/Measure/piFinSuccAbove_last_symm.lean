import Mathlib.MeasureTheory.MeasurableSpace.Embedding

namespace Commons.MeasureTheory.Measure

/-- The inverse of the measurable equivalence `MeasurableEquiv.piFinSuccAbove` at the last
coordinate is `Fin.snoc`, i.e. it appends the `α`-component as the last entry of the tuple. -/
theorem piFinSuccAbove_last_symm {n : ℕ} {α : Type*} [MeasurableSpace α] (p : α × (Fin n → α)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)).symm p
      = @Fin.snoc n (fun _ => α) p.2 p.1 := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rw [Fin.insertNthEquiv_last]
  ext x
  rw [Fin.snocEquiv_apply]

end Commons.MeasureTheory.Measure