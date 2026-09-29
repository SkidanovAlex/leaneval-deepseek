import Mathlib
import Submission.Commons.Data.Rat.finset_int_common_multiple

namespace Commons.Data.Rat

/-- For a finite family of rationals `c`, there is a positive natural `N`
such that `N * c i` is an integer for every `i`. -/
theorem exists_nat_mul_eq_int {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ m : ℤ, (N : ℚ) * c i = (m : ℚ) := by
  classical
  rcases finset_int_common_multiple (Finset.univ : Finset ι) c with ⟨D, hDne, hD⟩
  refine ⟨D, Nat.pos_of_ne_zero hDne, fun i => ?_⟩
  rcases hD i (Finset.mem_univ i) with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

end Commons.Data.Rat
