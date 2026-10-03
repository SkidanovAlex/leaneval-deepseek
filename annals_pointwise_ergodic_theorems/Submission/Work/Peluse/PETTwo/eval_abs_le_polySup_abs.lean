import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# `polySup` dominates `|P y|` on the whole interval `[-M, M]`

The definition `Work.Peluse.polySup P M = ∑_{i ≤ deg P} |a_i| M^i` is the explicit majorant for
`|P y|` on the integer interval `[-M, M]`.  The sibling module
`Submission/Work/Peluse/Tools/polySup_bound.lean` proves the one-sided version `0 ≤ y ≤ M`; here we
record the two-sided statement `|y| ≤ M`, which is what the `PET`/`PETTwo` chapters use (the
argument of the polynomial `P` is an arbitrary integer displacement).
-/

namespace Work.Peluse.PETTwo

open scoped BigOperators

/-- **The defining property of `polySup`, two-sided form.**  For every integer `y` with
`|y| ≤ M` one has `|P.eval y| ≤ polySup P M`. -/
theorem eval_abs_le_polySup_abs {P : Polynomial ℤ} {M : ℕ} {y : ℤ} (hy : |y| ≤ (M : ℤ)) :
    |P.eval y| ≤ ((Work.Peluse.polySup P M : ℕ) : ℤ) := by
  have hcast : ((Work.Peluse.polySup P M : ℕ) : ℤ)
      = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i).natAbs : ℤ) * (M : ℤ) ^ i := by
    simp only [Work.Peluse.polySup, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Polynomial.eval_eq_sum_range, hcast]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_pow]
  apply mul_le_mul
  · exact le_of_eq (Int.natCast_natAbs (P.coeff i)).symm
  · exact pow_le_pow_left₀ (abs_nonneg y) hy i
  · exact pow_nonneg (abs_nonneg y) i
  · exact Int.natCast_nonneg _

end Work.Peluse.PETTwo
