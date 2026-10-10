import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- The substitution `X i ↦ C (X i) * X` sends a monomial `monomial d a` to
`C (monomial d a) * X ^ (degree d)`: the variables contribute the monomial, the extra `X` records
the total degree. -/
lemma aeval_X_mul_X_monomial {σ R : Type*} [CommRing R] (d : σ →₀ ℕ) (a : R) :
    MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)
      (MvPolynomial.monomial d a)
      = Polynomial.C (MvPolynomial.monomial d a) * Polynomial.X ^ Finsupp.degree d := by
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply, ← MvPolynomial.C_eq_algebraMap]
  have h1 : d.prod (fun i k => (Polynomial.C (MvPolynomial.X i : MvPolynomial σ R) * Polynomial.X) ^ k)
      = d.prod (fun i k =>
          Polynomial.C (MvPolynomial.X i : MvPolynomial σ R) ^ k * Polynomial.X ^ k) := by
    apply Finsupp.prod_congr
    intro i _
    exact mul_pow _ _ _
  have h2 : d.prod (fun i k => Polynomial.C (MvPolynomial.X i : MvPolynomial σ R) ^ k)
      = Polynomial.C (MvPolynomial.monomial d 1) := by
    rw [Finsupp.prod_of_support_subset d (Finset.Subset.refl _) _ (fun i _ => by simp)]
    rw [show (∏ x ∈ d.support, Polynomial.C (MvPolynomial.X x : MvPolynomial σ R) ^ d x)
        = ∏ x ∈ d.support, Polynomial.C (MvPolynomial.X x ^ d x : MvPolynomial σ R) from
      Finset.prod_congr rfl (fun i _ => (map_pow _ _ _).symm)]
    rw [← map_prod, MvPolynomial.prod_X_pow_eq_monomial]
  have h3 : d.prod (fun i k => (Polynomial.X : Polynomial (MvPolynomial σ R)) ^ k)
      = Polynomial.X ^ Finsupp.degree d := by
    rw [Finsupp.prod_of_support_subset d (Finset.Subset.refl _) _ (fun i _ => by simp)]
    rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [h1, Finsupp.prod_mul, h2, h3, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]

/-- The coefficient of `X ^ k` in `aeval (fun i => C (X i) * X) f` is the `k`-th homogeneous
component of `f`. -/
lemma coeff_aeval_X_mul_X {σ R : Type*} [CommRing R] (f : MvPolynomial σ R) (k : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X) f).coeff k
      = MvPolynomial.homogeneousComponent k f := by
  have hmon : ∀ v : σ →₀ ℕ,
      (MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)
          (MvPolynomial.monomial v (f.coeff v))).coeff k
        = (if Finsupp.degree v = k then MvPolynomial.monomial v (f.coeff v) else 0) := by
    intro v
    rw [aeval_X_mul_X_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases hv : Finsupp.degree v = k
    · rw [ite_eq_left hv.symm, ite_eq_left hv]
    · rw [ite_eq_right (fun hh => hv hh.symm), ite_eq_right hv]
  rw [MvPolynomial.homogeneousComponent_apply, Finset.sum_filter]
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro v _
  exact hmon v

theorem isHomogeneous_of_aeval_smul {σ : Type*} {R : Type*} [CommRing R]
    (f : MvPolynomial σ R) (n : ℕ)
    (h : MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X) f
        = Polynomial.X ^ n * Polynomial.C f) :
    f.IsHomogeneous n := by
  have hnk : (Polynomial.X ^ n * Polynomial.C f).coeff n = f := by
    rw [mul_comm, Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl]
  have hn : MvPolynomial.homogeneousComponent n f = f := by
    rw [← coeff_aeval_X_mul_X f n, h, hnk]
  rw [← hn]
  exact MvPolynomial.homogeneousComponent_isHomogeneous n f

end Work.MotAS
