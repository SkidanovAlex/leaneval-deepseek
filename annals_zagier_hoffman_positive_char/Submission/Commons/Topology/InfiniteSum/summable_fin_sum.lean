import Mathlib.Topology.Algebra.InfiniteSum.Group
open scoped BigOperators

namespace Commons.Topology.InfiniteSum

/-! A finite sum (over a `Fintype`) of summable families is summable. -/

theorem summable_fin_sum {α : Type*} {β : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T0Space α] {ι : Type*} [Fintype ι]
    (g : ι → β → α) (hg : ∀ i, Summable (g i)) :
    Summable (fun d : β => ∑ i : ι, g i d) := by
  -- A finite sum of `HasSum`s has `HasSum` the sum of the limits (`hasSum_sum`),
  -- applied to the whole (finite) index type `ι`.
  have h : HasSum (fun d : β => ∑ i : ι, g i d) (∑ i : ι, ∑' d : β, g i d) := by
    simpa using
      (hasSum_sum (s := (Finset.univ : Finset ι)) (f := g)
        (a := fun i => ∑' d : β, g i d) (L := SummationFilter.unconditional β)
        (by intro i _; exact (hg i).hasSum))
  exact h.summable

end Commons.Topology.InfiniteSum
