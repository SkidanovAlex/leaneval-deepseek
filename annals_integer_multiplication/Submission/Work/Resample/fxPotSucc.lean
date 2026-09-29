import Mathlib
import Submission.Work.Fx.expRec

namespace Work.Resample

/-- Horner recursion for the error potential `pot`: shifting `d` down by one and `i` up by one
exposes the `k = 0` term.  Purely algebraic, so no sign hypothesis on `Z` is needed. -/
theorem fxPotSucc (Z : ℝ) (d i : ℕ) (hd : 1 ≤ d) :
    Work.Fx.pot Z (d - 1) (i + 1) = 1 + (Z / d) * Work.Fx.pot Z d i := by
  rw [Work.Fx.pot, Work.Fx.pot, Finset.sum_range_succ', Finset.mul_sum]
  have hf0 : Z ^ 0 * (((d - 1).factorial : ℝ) / ((d - 1 + 0).factorial : ℝ)) = 1 := by
    rw [pow_zero, Nat.add_zero, one_mul, div_self]
    exact_mod_cast Nat.factorial_ne_zero _
  rw [hf0]
  have hsum : (∑ k ∈ Finset.range i, Z ^ (k + 1) *
      (((d - 1).factorial : ℝ) / ((d - 1 + (k + 1)).factorial : ℝ)))
      = ∑ k ∈ Finset.range i,
          (Z / d) * (Z ^ k * ((d.factorial : ℝ) / ((d + k).factorial : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k _
    have hdk : d - 1 + (k + 1) = d + k := by omega
    rw [hdk]
    have hfac : ((d.factorial : ℕ) : ℝ) = (d : ℝ) * (((d - 1).factorial : ℕ) : ℝ) := by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      simp [Nat.factorial_succ]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hf0 : (((d - 1).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hf1 : (((d + k).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    rw [hfac, pow_succ]
    field_simp
  rw [hsum, add_comm]

end Work.Resample
