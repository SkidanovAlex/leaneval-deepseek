import Mathlib
import Submission.Work.DSCOH.Basic

open MvPolynomial

namespace Work.DSCOH

/-- If the coefficient at `k` of `monomial s 1 * p` is non-zero, then `s ≤ k`.
Indeed, a monomial appearing in `monomial s 1 * p` with a non-zero coefficient is of the
form `s + m` with `m` a monomial of `p`. -/
lemma le_of_coeff_monomial_mul_ne_zero {R : Type*} [CommSemiring R] {σ : Type*}
    {p : MvPolynomial σ R} {s k : σ →₀ ℕ}
    (h : (MvPolynomial.monomial s (1 : R) * p).coeff k ≠ 0) : s ≤ k := by
  by_contra hle
  rw [MvPolynomial.coeff_monomial_mul', ite_eq_right hle] at h
  exact h rfl

/-- If `X i ^ M * f = X j ^ N * g` with `i ≠ j`, then `X j ^ N` divides `f`.

This holds over an arbitrary commutative ring: the monomials `X^m` form a basis, and
multiplication by `X i ^ M` shifts the support by `M • eᵢ` while multiplication by `X j ^ N`
shifts it by `N • eⱼ`, so every monomial `X^m` occurring in `f` must satisfy `mⱼ ≥ N`. -/
theorem mvpoly_X_pow_mul_eq_dvd {A : Type*} [CommRing A] {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {f g : Poly A n} {M N : ℕ}
    (h : (MvPolynomial.X i : Poly A n) ^ M * f = (MvPolynomial.X j : Poly A n) ^ N * g) :
    (MvPolynomial.X j : Poly A n) ^ N ∣ f := by
  -- Every monomial of `f` has `j`-th exponent at least `N`.
  have key : ∀ m ∈ f.support, N ≤ m j := by
    intro m hm
    -- The coefficient of `X^(M • eᵢ + m)` in `Xᵢ^M * f` is the coefficient of `X^m` in `f`,
    -- hence non-zero; by the equality it is the corresponding coefficient in `Xⱼ^N * g`.
    have hc : ((MvPolynomial.X j : Poly A n) ^ N * g).coeff (Finsupp.single i M + m) ≠ 0 := by
      rw [← h, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul]
      simpa using (MvPolynomial.mem_support_iff.mp hm)
    rw [MvPolynomial.X_pow_eq_monomial] at hc
    -- A non-zero coefficient of `Xⱼ^N * g` at `k` forces `N • eⱼ ≤ k`, i.e. `N ≤ k j`.
    have := (Finsupp.single_le_iff.mp (le_of_coeff_monomial_mul_ne_zero hc) :
      N ≤ (Finsupp.single i M + m) j)
    simpa [Finsupp.add_apply, hij] using this
  -- Each monomial `X^m` of `f` is divisible by `Xⱼ^N`.
  rw [MvPolynomial.as_sum f, MvPolynomial.X_pow_eq_monomial]
  refine Finset.dvd_sum fun m hm => MvPolynomial.monomial_dvd_monomial.mpr
    ⟨Or.inr (Finsupp.single_le_iff.mpr (key m hm)), one_dvd _⟩

end Work.DSCOH
