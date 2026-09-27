import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp

open MeasureTheory

-- namespace Work.EKLComp; imports Mathlib, Submission.Work.EKLComp.Hcond; open MeasureTheory
-- Needed at `X : Type*` (the existing `Work.EKLComp.condExp_inter_indicator_localize` in
-- Submission/Work/EKLComp/Hcond_joinPart.lean is stated at `X : Type`).
theorem condExp_inter_indicator_localize_poly {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {ι : Type*} [Fintype ι] (A : ι → Set X) (hA : Work.EKLComp.Core.IsMPart A) (hm : m ≤ mX)
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] (i : ι) (S : Set X)
    (hS : MeasurableSet S) :
    MeasureTheory.condExp (m ⊔ Work.EKLComp.Core.partSigmaFam A) μ ((A i ∩ S).indicator (fun _ => (1:ℝ)))
      =ᵐ[μ] (A i).indicator (fun _ => (1:ℝ))
        * MeasureTheory.condExp (m ⊔ Work.EKLComp.Core.partSigmaFam A) μ (S.indicator (fun _ => (1:ℝ))) := by
  have hAi_le : Core.partSigmaFam A ≤ m ⊔ Core.partSigmaFam A := le_sup_right
  have hAi : MeasurableSet[m ⊔ Core.partSigmaFam A] (A i) :=
    hAi_le _ (MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩)
  have hfun : ((A i).indicator (fun _ => (1:ℝ))) * (S.indicator (fun _ => (1:ℝ)))
      = ((A i ∩ S).indicator (fun _ => (1:ℝ))) := by
    funext x
    by_cases hx : x ∈ A i <;> by_cases hy : x ∈ S <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
  rw [← hfun]
  refine condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m ⊔ Core.partSigmaFam A)
    (f := (A i).indicator (fun _ => (1:ℝ))) (g := S.indicator (fun _ => (1:ℝ)))
    ?_ ?_ ?_
  · exact (measurable_const.indicator hAi).stronglyMeasurable
  · rw [hfun]
    exact (integrable_const (1:ℝ)).indicator ((hA.measurable i).inter hS)
  · exact (integrable_const (1:ℝ)).indicator hS

end Work.EKLComp
