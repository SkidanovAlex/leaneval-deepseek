import Mathlib
import Submission.Work.EKLComp.FinPartLevel

namespace Work.EKLComp

theorem levelCell_measurable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    (e : ι ≃ Fin (Fintype.card ι)) (U C : ι → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hC : ∀ i, MeasurableSet (C i)) :
    (∀ m, MeasurableSet (Work.EKLComp.levelCell e U C m)) ∧
      MeasurableSet (Work.EKLComp.levelCore C) := by
  refine ⟨fun m => ?_, ?_⟩
  · exact (hU _).inter (MeasurableSet.iInter fun j => hC _)
  · exact MeasurableSet.iInter fun i => hC i

end Work.EKLComp
