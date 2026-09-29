import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_ge

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- The `min` rule for a finite sum: if every summand has order at least `N`, so does the sum. -/
theorem le_ordAtT_finset_sum {K : Type*} [Field K] {α : K} {ι : Type*} {s : Finset ι}
    {f : ι → RatFunc K} {N : ℤ} (h : ∀ i ∈ s, (N : WithTop ℤ) ≤ ordAtT α (f i)) :
    (N : WithTop ℤ) ≤ ordAtT α (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      have : ordAtT α (0 : RatFunc K) = ⊤ := by simp [ordAtT]
      rw [this]
      exact le_top
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have ha' : (N : WithTop ℤ) ≤ ordAtT α (f a) := h a (Finset.mem_insert_self a s)
      have hs' : (N : WithTop ℤ) ≤ ordAtT α (∑ i ∈ s, f i) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      calc (N : WithTop ℤ) = min (N : WithTop ℤ) N := by simp
        _ ≤ min (ordAtT α (f a)) (ordAtT α (∑ i ∈ s, f i)) := min_le_min ha' hs'
        _ ≤ ordAtT α (f a + ∑ i ∈ s, f i) := ordAtT_add_ge α _ _

end Commons.FieldTheory.RatFunc
