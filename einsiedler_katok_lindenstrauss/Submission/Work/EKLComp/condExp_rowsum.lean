import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp

theorem condExp_rowsum {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ] (A : ι → Set X) (B : κ → Set X)
    (hA : Work.EKLComp.Core.IsMPart A) (hB : Work.EKLComp.Core.IsMPart B)
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] (i : ι) :
    (∑ j, MeasureTheory.condExp m μ ((A i ∩ B j).indicator (fun _ => (1 : ℝ))))
      =ᵐ[μ] MeasureTheory.condExp m μ ((A i).indicator (fun _ => (1 : ℝ))) := by
  classical
  -- Pointwise: `∑ j, 1_{A i ∩ B j} = 1_{A i}`, since `B` is a finite partition.
  have hpt : ∀ x, (∑ j, (A i ∩ B j).indicator (fun _ => (1 : ℝ)) x)
      = (A i).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ A i
    · obtain ⟨j0, hj0, huniq⟩ := hB.exists_unique x
      rw [Finset.sum_eq_single_of_mem j0 (Finset.mem_univ j0)]
      · rw [Set.indicator_of_mem (show x ∈ A i ∩ B j0 from ⟨hx, hj0⟩),
          Set.indicator_of_mem hx]
      · intro j _ hj
        rw [Set.indicator_of_notMem]
        intro hmem
        exact hj (huniq j hmem.2)
    · rw [Set.indicator_of_notMem hx, Finset.sum_eq_zero]
      intro j _
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hx hmem.1
  -- Each summand is integrable (indicator of a finite-measure set).
  have hint : ∀ j, MeasureTheory.Integrable ((A i ∩ B j).indicator (fun _ => (1 : ℝ))) μ := by
    intro j
    refine (MeasureTheory.integrable_indicator_iff
      ((hA.measurable i).inter (hB.measurable j))).2 ?_
    exact MeasureTheory.integrableOn_const (MeasureTheory.measure_ne_top μ _)
  -- Conditional expectation is linear over finite sums.
  have h1 := MeasureTheory.condExp_finsetSum (s := Finset.univ)
    (f := fun j => (A i ∩ B j).indicator (fun _ => (1 : ℝ))) (fun j _ => hint j) m
  exact h1.symm.trans (MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq (by
    funext x
    simpa only [Finset.sum_apply] using hpt x)))

end Work.EKLComp
