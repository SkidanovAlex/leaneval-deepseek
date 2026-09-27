import Mathlib
import Submission.Work.EKLComp.Hcond

open MeasureTheory
open scoped BigOperators

namespace Work.EKLComp

/-- Slicing a measurable set by the finite union of parts of a measurable partition indexed by a
`Finset`, in real-valued probability form. -/
theorem real_inter_iUnion_atoms {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {ι : Type} [Fintype ι] {A : ι → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (s : Finset ι) {T : Set X} (hT : MeasurableSet T) :
    (μ (T ∩ ⋃ i ∈ s, A i)).toReal = ∑ i ∈ s, (μ (T ∩ A i)).toReal := by
  have hm : ∀ i ∈ s, MeasurableSet (T ∩ A i) := fun i _ => hT.inter (hA.measurable i)
  have hd : (↑s : Set ι).PairwiseDisjoint (fun i => T ∩ A i) := by
    intro i _ j _ hij
    exact (hA.disjoint hij).mono Set.inter_subset_right Set.inter_subset_right
  have hset : T ∩ ⋃ i ∈ s, A i = ⋃ i ∈ s, T ∩ A i :=
    Set.inter_iUnion₂ T (fun i (_ : i ∈ s) => A i)
  rw [hset, measure_biUnion_finset hd hm,
    ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]

end Work.EKLComp
