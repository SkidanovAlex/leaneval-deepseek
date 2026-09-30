import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Logarithmic derivative identity for the torus monomial `∏_j Y_j^{μ_j}`, where `Y_j = X_{j+1}`:
differentiating in `Y_i` and multiplying back by `Y_i` multiplies the monomial by `μ_i`. -/
theorem X_succ_mul_pderiv_prod_X_succ_pow {r : ℕ} (i : Fin r) (μ : Fin r → ℕ) :
    MvPolynomial.X i.succ * (MvPolynomial.pderiv i.succ)
        (∏ j : Fin r, MvPolynomial.X j.succ ^ (μ j))
      = MvPolynomial.C ((μ i : ℕ) : ℂ) * ∏ j : Fin r, MvPolynomial.X j.succ ^ (μ j) := by
  classical
  -- Write the monomial `∏_j X_{j+1}^{μ_j}` as a single monomial, with exponent vector
  -- `F = ∑_j μ_j · e_{j+1}`.
  set F : Fin (r + 1) →₀ ℕ := ∑ j : Fin r, Finsupp.single j.succ (μ j) with hF
  have hP : (∏ j : Fin r, (MvPolynomial.X j.succ : MvPolynomial (Fin (r + 1)) ℂ) ^ (μ j))
      = MvPolynomial.monomial F (1 : ℂ) := by
    simp_rw [MvPolynomial.X_pow_eq_monomial]
    rw [← MvPolynomial.monomial_sum_one Finset.univ
      (fun j : Fin r => Finsupp.single j.succ (μ j))]
  -- The exponent of `X_{i+1}` in `F` is exactly `μ i`.
  have hFi : F i.succ = μ i := by
    rw [hF, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Fin.succ_inj, hb]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hP, MvPolynomial.X_mul_pderiv_monomial, hFi]
  rw [MvPolynomial.C_mul', Nat.cast_smul_eq_nsmul]

end Work.BW
