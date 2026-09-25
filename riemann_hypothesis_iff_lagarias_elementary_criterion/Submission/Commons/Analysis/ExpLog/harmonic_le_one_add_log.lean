import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace Commons.Analysis.ExpLog

/-- The harmonic sum up to `A` is bounded by `1 + log A`.

This transports Mathlib's `harmonic_le_one_add_log` (which bounds the
`ℚ`-valued harmonic sum) to the real-valued sum over `Finset.Icc`. -/
theorem harmonic_le_one_add_log (A : ℕ) (hA : 1 ≤ A) :
    (∑ k ∈ Finset.Icc 1 A, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (A : ℝ) := by
  have h_eq : (∑ k ∈ Finset.Icc 1 A, (1 : ℝ) / (k : ℝ)) = (harmonic A : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Rat.cast_inv]
    simp
  rw [h_eq]
  exact _root_.harmonic_le_one_add_log A

end Commons.Analysis.ExpLog