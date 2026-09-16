import Mathlib
import Submission.Commons.Algebra.Sum.sum_range_filter

namespace Commons.Algebra.Sum

theorem sum_fiber_range_list {α M : Type*} [AddCommMonoid M] (l : List α) (g : α → ℕ) (n : ℕ) (F : α → M) (h : ∀ x ∈ l, g x < n) :
    (l.map F).sum = ((List.range n).map (fun i => ((l.filter (fun x => decide (g x = i))).map F).sum)).sum := by
  -- The list `List.range n` is (as a multiset) exactly `Finset.range n`, so the
  -- iterated list sum on the right is the corresponding Finset sum.
  rw [show ((List.range n).map (fun i => ((l.filter (fun x => decide (g x = i))).map F).sum)).sum
      = ∑ i ∈ Finset.range n, ((l.filter (fun x => decide (g x = i))).map F).sum from by
    rw [Finset.sum_eq_multiset_sum]; rfl]
  exact (sum_range_filter l g n F h).symm

end Commons.Algebra.Sum
