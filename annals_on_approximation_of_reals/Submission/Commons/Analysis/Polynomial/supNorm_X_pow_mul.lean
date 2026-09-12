import Mathlib.Analysis.Polynomial.Norm

namespace Commons.Analysis.Polynomial

/-- Multiplying a polynomial by a power of `X` shifts its coefficients, so the supremum of the
norms of the coefficients (the sup norm) is unchanged. -/
theorem supNorm_X_pow_mul {A : Type*} [NormedRing A] (Q : Polynomial A) (t : ℕ) :
    ((Polynomial.X ^ t : Polynomial A) * Q).supNorm = Q.supNorm := by
  apply le_antisymm
  · -- supNorm (X^t * Q) ≤ supNorm Q
    obtain ⟨i, hi⟩ := Polynomial.exists_eq_supNorm (p := (Polynomial.X ^ t : Polynomial A) * Q)
    rw [hi]
    by_cases h : t ≤ i
    · rw [Polynomial.coeff_X_pow_mul' Q t i, if_pos h]
      exact Polynomial.le_supNorm Q (i - t)
    · rw [Polynomial.coeff_X_pow_mul' Q t i, if_neg h]
      simpa using Polynomial.supNorm_nonneg Q
  · -- supNorm Q ≤ supNorm (X^t * Q)
    obtain ⟨j, hj⟩ := Polynomial.exists_eq_supNorm (p := Q)
    rw [hj]
    have hle := Polynomial.le_supNorm (p := (Polynomial.X ^ t : Polynomial A) * Q) (j + t)
    rwa [Polynomial.coeff_X_pow_mul Q t j] at hle

end Commons.Analysis.Polynomial