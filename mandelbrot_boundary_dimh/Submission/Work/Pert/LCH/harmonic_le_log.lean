import Mathlib

namespace Work.Pert.LCH

open Finset

/-- The `N`-th harmonic number is at most `1 + log N`: this is the classical
integral-comparison bound `∑_{i=1}^{N} 1/i ≤ 1 + ∫_1^N dx/x`, available in Mathlib as
`harmonic_le_one_add_log`.  Here it is written with the sum unfolded into the range of
the `N` terms `1/(i+1)`. -/
theorem harmonic_le_log (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1)) ≤ 1 + Real.log (N : ℝ) := by
  have h : (harmonic N : ℝ) = ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
    rw [show (harmonic N : ℝ) = ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℚ) : ℝ)⁻¹ from by
          simp [harmonic, Rat.cast_sum, Rat.cast_inv]]
    apply Finset.sum_congr rfl
    intro i _
    rw [inv_eq_one_div]
    push_cast
    ring
  rw [← h]
  exact harmonic_le_one_add_log N

end Work.Pert.LCH
