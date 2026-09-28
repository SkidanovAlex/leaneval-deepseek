import Mathlib

namespace Work.HP.MM2

/-- The `M`-th partial sum of the harmonic series is at most `1 + log M`.
Proved by comparing with Mathlib's harmonic-number bound
`harmonic_le_one_add_log`. -/
theorem ss1_sum_Icc_inv_le (M : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ≤ 1 + Real.log M := by
  have h := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at h
  simpa [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using h

end Work.HP.MM2
