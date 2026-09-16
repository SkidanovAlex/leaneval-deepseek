import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped BigOperators

/-! Finite sums commute with tsums over a countable type, provided each inner family is
summable. -/

namespace Commons.Topology.InfiniteSum

theorem fin_sum_tsum {α : Type*} {β : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T0Space α] {ι : Type*} [Fintype ι]
    (g : ι → β → α) (hg : ∀ i, Summable (fun d : β => g i d)) :
    (∑ i : ι, ∑' d : β, g i d) = ∑' d : β, (∑ i : ι, g i d) := by
  -- The finite sum of `HasSum`s has `HasSum` the sum of the limits (`hasSum_sum`),
  -- applied to the whole (finite) index type `ι`.
  have h : HasSum (fun d : β => ∑ i ∈ (Finset.univ : Finset ι), g i d)
      (∑ i ∈ (Finset.univ : Finset ι), ∑' d : β, g i d) := by
    refine hasSum_sum (s := (Finset.univ : Finset ι)) (f := g)
      (a := fun i => ∑' d : β, g i d) ?_
    intro i _
    exact (hg i).hasSum
  -- `HasSum.tsum_eq` identifies the tsum of the right-hand family with its limit,
  -- which is exactly the finite sum of the column tsums.  The `univ` sums over `ι`
  -- are definitionally the `∑ i : ι, ...` notation of the statement.
  exact h.tsum_eq.symm

end Commons.Topology.InfiniteSum
