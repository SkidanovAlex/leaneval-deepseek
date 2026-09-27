import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp

/-- The sum of the indicators of the parts of an `IsMPart` family is identically `1`. -/
theorem sum_indicator_isMPart_eq_one {X : Type} [mX : MeasurableSpace X]
    {κ : Type} [Fintype κ] (B : κ → Set X) (hB : Work.EKLComp.Core.IsMPart B) :
    (∑ j, (B j).indicator (fun _ => (1 : ℝ))) = (fun _ => (1 : ℝ)) := by
  funext x
  rw [Finset.sum_apply]
  obtain ⟨i, hi, huniq⟩ := hB.exists_unique x
  have hsingle : ∀ j ≠ i, (B j).indicator (fun _ => (1 : ℝ)) x = 0 := by
    intro j hj
    rw [Set.indicator_of_notMem]
    exact fun hxj => hj (huniq j hxj)
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi]
  · intro j _ hj
    exact hsingle j hj
  · intro hi'; exact absurd (Finset.mem_univ i) hi'

theorem condExp_sum_one {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {κ : Type} [Fintype κ] (B : κ → Set X)
    (hB : Work.EKLComp.Core.IsMPart B) (hm : m ≤ mX)
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] :
    (∑ j, MeasureTheory.condExp m μ ((B j).indicator (fun _ => (1 : ℝ))))
      =ᵐ[μ] (fun _ => (1:ℝ)) := by
  have hfun := sum_indicator_isMPart_eq_one B hB
  have hint : ∀ j, MeasureTheory.Integrable ((B j).indicator (fun _ => (1 : ℝ))) μ :=
    fun j => (MeasureTheory.integrable_const (1 : ℝ)).indicator (hB.measurable j)
  calc (∑ j, MeasureTheory.condExp m μ ((B j).indicator (fun _ => (1 : ℝ))))
      =ᵐ[μ] MeasureTheory.condExp m μ (∑ j, (B j).indicator (fun _ => (1 : ℝ))) := by
        simpa using (MeasureTheory.condExp_finsetSum (s := Finset.univ)
          (f := fun j => (B j).indicator (fun _ => (1 : ℝ)))
          (fun j _ => hint j) m).symm
    _ =ᵐ[μ] MeasureTheory.condExp m μ (fun _ => (1 : ℝ)) := by rw [hfun]
    _ =ᵐ[μ] (fun _ => (1 : ℝ)) :=
        Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const hm (1 : ℝ))

end Work.EKLComp
