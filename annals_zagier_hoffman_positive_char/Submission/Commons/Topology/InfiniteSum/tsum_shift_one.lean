import Mathlib.Topology.Algebra.InfiniteSum.NatInt
open scoped BigOperators

namespace Commons.Topology.InfiniteSum

/-! Shifting a summable sequence over ℕ by one drops its first term. -/

theorem tsum_shift_one {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
    [CompleteSpace α] [T0Space α] {x : ℕ → α} (hx : Summable x) :
    (∑' d : ℕ, x (d + 1)) = (∑' d : ℕ, x d) - x 0 := by
  calc
    (∑' d : ℕ, x (d + 1)) = (x 0 + ∑' d : ℕ, x (d + 1)) - x 0 := by
      abel
    _ = (∑' d : ℕ, x d) - x 0 := by
      rw [Summable.tsum_eq_zero_add hx]

end Commons.Topology.InfiniteSum
