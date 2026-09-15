import Mathlib.Algebra.Field.ZMod
import Submission.Commons.Combinatorics.Additive.AP.sum_of_coordinates

namespace Commons.Combinatorics.Additive.AP

theorem sum_of_coords {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (g : ZMod p → ℝ) :
    (∑ y : Fin n → ZMod p, g (∑ i, y i)) = (p : ℝ)^(n-1) * ∑ x : ZMod p, g x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  rw [Nat.add_sub_cancel, sum_of_coordinates m g, ZMod.card p]

end Commons.Combinatorics.Additive.AP