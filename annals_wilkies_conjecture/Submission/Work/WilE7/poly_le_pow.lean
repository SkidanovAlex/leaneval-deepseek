import Mathlib

namespace Work.WilE7

/-- A polynomial in two variables with coefficients in `ℕ` is bounded by
`M * (1 + D)^N * (1 + k)^N` for suitable `M`, `N` (namely the sum of the
coefficients and the total degree). -/
theorem poly_le_pow (b : MvPolynomial (Fin 2) ℕ) :
    ∃ (M N : ℕ), ∀ D k : ℕ, b.eval ![D, k] ≤ M * (1 + D) ^ N * (1 + k) ^ N := by
  -- Sum of all coefficients bounds the "constant" and the total degree bounds both exponents.
  refine ⟨∑ d ∈ b.support, b.coeff d, b.totalDegree, fun D k => ?_⟩
  -- Each monomial's contribution is bounded by `coeff * (1+D)^N * (1+k)^N`.
  have hkey : ∀ d ∈ b.support,
      b.coeff d * (D ^ d 0 * k ^ d 1)
        ≤ b.coeff d * ((1 + D) ^ b.totalDegree * (1 + k) ^ b.totalDegree) := by
    intro d hd
    have h0 : d 0 ≤ b.totalDegree :=
      (MvPolynomial.le_degreeOf_of_mem_support 0 hd).trans (MvPolynomial.degreeOf_le_totalDegree b 0)
    have h1 : d 1 ≤ b.totalDegree :=
      (MvPolynomial.le_degreeOf_of_mem_support 1 hd).trans (MvPolynomial.degreeOf_le_totalDegree b 1)
    have hD : D ^ d 0 ≤ (1 + D) ^ b.totalDegree :=
      (Nat.pow_le_pow_left (by omega) (d 0)).trans (Nat.pow_le_pow_right (by omega) h0)
    have hk : k ^ d 1 ≤ (1 + k) ^ b.totalDegree :=
      (Nat.pow_le_pow_left (by omega) (d 1)).trans (Nat.pow_le_pow_right (by omega) h1)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hD hk)
  calc b.eval ![D, k]
      = ∑ d ∈ b.support, b.coeff d * (D ^ d 0 * k ^ d 1) := by
        rw [MvPolynomial.eval_eq']
        apply Finset.sum_congr rfl
        intro d _
        congr 1
        rw [Fin.prod_univ_two]
        simp
    _ ≤ ∑ d ∈ b.support, b.coeff d * ((1 + D) ^ b.totalDegree * (1 + k) ^ b.totalDegree) :=
        Finset.sum_le_sum hkey
    _ = (∑ d ∈ b.support, b.coeff d) * ((1 + D) ^ b.totalDegree * (1 + k) ^ b.totalDegree) := by
        rw [← Finset.sum_mul]
    _ = (∑ d ∈ b.support, b.coeff d) * (1 + D) ^ b.totalDegree * (1 + k) ^ b.totalDegree := by
        ring

end Work.WilE7
