import Mathlib
import Submission.Work.EKLComp.USCBasic

namespace Work.EKLComp

open MeasureTheory Set

/-- Poincaré recurrence for a countable family of measurable sets: for a measure preserving
self-map `T` of a probability space, almost every point `x` that lies in some `B i` returns to
`B i` after a positive number of iterations. -/
theorem recurrence_family {T : Work.EKLContract.X3 → Work.EKLContract.X3} {ν : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure ν] (hmp : MeasureTheory.MeasurePreserving T ν ν) {ι : Type*} [Countable ι] (B : ι → Set Work.EKLContract.X3) (hB : ∀ i, MeasurableSet (B i)) : ∃ N : Set Work.EKLContract.X3, ν N = 0 ∧ ∀ x ∉ N, ∀ i, x ∈ B i → ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ B i := by
  classical
  have hc : MeasureTheory.Conservative T ν := hmp.conservative
  refine ⟨⋃ i, {x | x ∈ B i ∧ ∀ m ≥ 1, T^[m] x ∉ B i}, ?_, ?_⟩
  · apply measure_iUnion_null
    intro i
    exact hc.measure_mem_forall_ge_image_notMem_eq_zero (hB i).nullMeasurableSet 1
  · intro x hx i hxi
    have hbad : x ∉ ({x | x ∈ B i ∧ ∀ m ≥ 1, T^[m] x ∉ B i} : Set _) :=
      fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)
    by_contra hcon
    exact hbad ⟨hxi, fun m hm hmem => hcon ⟨m, hm, hmem⟩⟩

end Work.EKLComp
