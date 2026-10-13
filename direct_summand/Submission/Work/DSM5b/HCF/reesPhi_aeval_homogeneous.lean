import Mathlib
import Submission.Work.DSM5b.HCF.ReesDefs

namespace Work.DSM5b.HCF

universe u

/-- **The Rees map on a form**: for a form `f` of degree `d`, `reesPhi t` (the `R`-algebra map
`R[X_0,…,X_{n-1}] → R[u]` with `X_i ↦ C (t i) * X`, see `Submission/Work/DSM5b/HCF/ReesDefs.lean`)
sends `f` to `C c * X^d` with `c = aeval t f`, where `aeval t : R[X_0,…,X_{n-1}] → R` evaluates
`X_i ↦ t i`.  Route: `MvPolynomial.as_sum` writes `f = ∑ a ∈ f.support, monomial a (f.coeff a)`,
`reesPhi_monomial` computes each summand, and `f.IsHomogeneous d` says `a.degree = d` for every
`a ∈ f.support`, so the sum is `C (∑ …) * X^d` with `∑ … = aeval t f` (e.g. by
`MvPolynomial.eval₂_eq`). -/
theorem reesPhi_aeval_homogeneous {n : ℕ} {R : Type u} [CommRing R] (t : Fin n → R)
    {f : Work.DSCOH.Poly R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    reesPhi t f = Polynomial.C (MvPolynomial.aeval t f) * Polynomial.X ^ d := by
  classical
  -- The Finsupp sum `a.sum fun _ k => k` is the total degree of `a`.
  have hsum : ∀ a : Fin n →₀ ℕ, a.sum (fun _ k => k) = a.degree := fun a => by
    rw [Finsupp.degree_apply, Finsupp.sum]
  -- Every monomial occurring in `f` has degree `d`.
  have hdeg : ∀ a ∈ f.support, a.degree = d := by
    intro a ha
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp ha) (MvPolynomial.IsHomogeneous.coeff_eq_zero hf h)
  -- The Rees map sends the monomial `coeff a • X^a` to `C (coeff a * t^a) * X^d`.
  have hterm : ∀ a ∈ f.support, reesPhi t (MvPolynomial.monomial a (f.coeff a))
      = Polynomial.C (f.coeff a * a.prod (fun i k => t i ^ k)) * Polynomial.X ^ d := by
    intro a ha
    rw [reesPhi_monomial, hsum a, hdeg a ha]
  -- The evaluation of `f` at `t` is the sum of the coefficients `coeff a * t^a`.
  have haeval : MvPolynomial.aeval t f
      = ∑ a ∈ f.support, f.coeff a * a.prod (fun i k => t i ^ k) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPolynomial.aeval_monomial]
    simp
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, ← haeval]

end Work.DSM5b.HCF
