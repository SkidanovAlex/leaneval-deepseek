import Mathlib
import Submission.Work.DSCOH.LocBasisDefs

namespace Work.DSCOH

/-- The monomials `x^α = ∏ᵢ Xᵢ^{αᵢ}` (`α : Fin n → ℕ`) are linearly independent over `A`. This is
the monomial basis `MvPolynomial.basisMonomials` of `A[X₀,…,X_{n-1}]`, transported across the
bijection `(Fin n →₀ ℕ) ≃ (Fin n → ℕ)` given by `Finsupp.equivFunOnFinite`, using that
`monomial v 1 = xpow (fun i => v i)`. -/
theorem lmb_xpow_linearIndependent {A : Type*} [CommRing A] {n : ℕ} :
    LinearIndependent A (fun α : Fin n → ℕ => xpow (A := A) (n := n) α) := by
  -- The monomials indexed by finitely supported exponent vectors form a basis.
  have hbase : LinearIndependent A
      (fun s : Fin n →₀ ℕ => (MvPolynomial.monomial s) (1 : A)) := by
    simpa only [MvPolynomial.coe_basisMonomials] using
      (MvPolynomial.basisMonomials (Fin n) A).linearIndependent
  -- Reindex along the bijection `(Fin n →₀ ℕ) ≃ (Fin n → ℕ)`.
  have hfun : (fun α : Fin n → ℕ => xpow (A := A) (n := n) α)
      = (fun s : Fin n →₀ ℕ => (MvPolynomial.monomial s) (1 : A)) ∘
        (Finsupp.equivFunOnFinite.symm : (Fin n → ℕ) → (Fin n →₀ ℕ)) := by
    funext α
    simp only [Function.comp_apply]
    rw [mvpoly_monomial_eq_xpow]
    congr 1
  rw [hfun]
  exact hbase.comp _ Finsupp.equivFunOnFinite.symm.injective

end Work.DSCOH
