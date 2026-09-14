import Mathlib.Algebra.MvPolynomial.Equiv

namespace Commons.Algebra.MvPolynomial

theorem uniqueAlgEquiv_coeff {σ : Type*} [Unique σ] (P : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (MvPolynomial.uniqueAlgEquiv ℚ σ P).coeff (d default) = P.coeff d := by
  rw [MvPolynomial.coeff_uniqueAlgEquiv, ← Finsupp.unique_single d]

end Commons.Algebra.MvPolynomial