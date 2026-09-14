import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Submission.Commons.Data.Rat.finset_int_common_multiple

namespace Commons.Data.Rat

/-- Every finite family of rationals has a common positive integer denominator:
each `q i` can be written as an integer over the same natural `D`. -/
theorem exists_common_denominator (ι : Type*) [Fintype ι] (q : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i : ι, ∃ n : ℤ, (q i : ℚ) = (n : ℚ) / D := by
  classical
  rcases finset_int_common_multiple (Finset.univ : Finset ι) q with ⟨D, hDne, hD⟩
  refine ⟨D, Nat.pos_of_ne_zero hDne, ?_⟩
  intro i
  rcases hD i (Finset.mem_univ i) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hDne' : (D : ℚ) ≠ 0 := by exact_mod_cast hDne
  rw [hz]
  exact (mul_div_cancel_left₀ (q i) hDne').symm

end Commons.Data.Rat