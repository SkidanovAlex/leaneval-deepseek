import Mathlib.NumberTheory.NumberField.Discriminant.Basic

namespace Commons.NumberTheory.NumberField

/-- The root discriminant of a number field is at least `1` (in fact strictly
positive).  This is needed, e.g., to take `C := rootDiscr B` as the positive
constant in Martinet's asymptotically-good totally real towers.

Proof hints: `(discr K).natAbs ≠ 0` by `NumberField.discr_ne_zero`
(equivalently `NumberField.discr_not_zero_of_basis`), so as real numbers
`1 ≤ |(discr K : ℝ)|`; the degree `Module.finrank ℚ K` is positive
(`Module.finrank_pos`); raise both sides to the positive power
`(Module.finrank ℚ K : ℝ)⁻¹` using `Real.rpow_le_rpow` (or the
`rpow_inv_le_iff`-style equivalences), then unfold
`NumberField.rootDiscr_def`. -/
theorem one_le_rootDiscr (K : Type*) [Field K] [NumberField K] :
    1 ≤ NumberField.rootDiscr K := by
  rw [NumberField.rootDiscr_def]
  refine Real.one_le_rpow ?hx ?hz
  · -- `1 ≤ |discr K|` as real numbers, because `discr K ≠ 0` is an integer
    have hna1 : 1 ≤ (NumberField.discr K).natAbs := by
      exact Nat.succ_le_of_lt (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    have h_int : (1 : ℤ) ≤ |NumberField.discr K| := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hna1
    exact_mod_cast h_int
  · -- the exponent `(finrank ℚ K)⁻¹` is nonnegative
    positivity

end Commons.NumberTheory.NumberField