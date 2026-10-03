import Mathlib

namespace Work.FIArea5.HeckeZFR.Hadm

/-- If `Θ z = z ^ k * ψ z` for all `z` and `Θ` satisfies a circle growth bound of shape
`log ‖Θ z‖ ≤ C·R·(log (R+2) + K)` on `‖z‖ = R ≥ 1`, then `ψ` satisfies a bound of the same shape
(with the same `C, K`). -/
theorem growthFactor {Θ ψ : ℂ → ℂ} {k : ℕ} (hfac : ∀ z : ℂ, Θ z = z ^ k * ψ z)
    (hgr : ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Θ z‖ ≤ C * R * (Real.log (R + 2) + K)) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖ψ z‖ ≤ C * R * (Real.log (R + 2) + K) := by
  obtain ⟨C, K, hC, hK, hbound⟩ := hgr
  refine ⟨C, K, hC, hK, ?_⟩
  intro R hR z hz
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rcases eq_or_ne ‖ψ z‖ 0 with h0 | hne
  · -- ψ z = 0 : log ‖ψ z‖ = 0 ≤ RHS since RHS ≥ 0
    rw [h0, Real.log_zero]
    have hlog : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have : 0 ≤ C * R * (Real.log (R + 2) + K) :=
      mul_nonneg (mul_nonneg (le_of_lt hC) (le_of_lt hRpos)) (by linarith)
    linarith
  · -- ‖ψ z‖ ≠ 0 : split the log of the product
    have hψpos : 0 < ‖ψ z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
    have hRk : 0 < R ^ k := pow_pos hRpos k
    have hnorm : ‖Θ z‖ = R ^ k * ‖ψ z‖ := by
      rw [hfac z, norm_mul, norm_pow, hz]
    have hsplit : Real.log ‖Θ z‖ = (k : ℝ) * Real.log R + Real.log ‖ψ z‖ := by
      rw [hnorm, Real.log_mul (ne_of_gt hRk) (ne_of_gt hψpos), Real.log_pow]
    have hb := hbound R hR z hz
    have hklog : 0 ≤ (k : ℝ) * Real.log R := mul_nonneg (Nat.cast_nonneg k) hlogR
    linarith

end Work.FIArea5.HeckeZFR.Hadm
