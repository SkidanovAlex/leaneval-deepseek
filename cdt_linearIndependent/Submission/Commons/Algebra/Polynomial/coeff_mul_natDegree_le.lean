import Mathlib.Algebra.Polynomial.Degree.Operations

namespace Commons.Algebra.Polynomial

/-- The `(a+b)`-th coefficient of a product `A * B` with `natDegree A ≤ a` and
`natDegree B ≤ b` is the product of the `a`-th coefficient of `A` and the
`b`-th coefficient of `B`: all other contributions to the antidiagonal sum
vanish because a coefficient beyond the `natDegree` is zero. -/
theorem coeff_mul_natDegree_le {R : Type*} [Semiring R] (A B : Polynomial R) (a b : ℕ)
    (hA : A.natDegree ≤ a) (hB : B.natDegree ≤ b) :
    (A * B).coeff (a + b) = A.coeff a * B.coeff b := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨i, j⟩ hmem hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
    rcases lt_trichotomy i a with h | h | h
    · have hjb : b < j := by omega
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hB hjb)]
    · have hj : j = b := by omega
      exact absurd (by simp [h, hj]) hne
    · have hi : A.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hA h)
      simp [hi]
  · intro h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact absurd rfl h

end Commons.Algebra.Polynomial