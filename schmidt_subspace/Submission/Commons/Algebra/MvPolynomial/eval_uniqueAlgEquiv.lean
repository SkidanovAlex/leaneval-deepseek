import Mathlib.Algebra.MvPolynomial.Equiv

namespace Commons.Algebra.MvPolynomial

theorem eval_uniqueAlgEquiv {σ : Type*} [Unique σ] (β : σ → ℚ) (P : MvPolynomial σ ℚ) :
    MvPolynomial.eval β P = (MvPolynomial.uniqueAlgEquiv ℚ σ P).eval (β default) := by
  rw [← MvPolynomial.eval₂_id (g := β)]
  rw [← MvPolynomial.eval₂_uniqueAlgEquiv (φ := RingHom.id ℚ) (a := β)]
  rw [Polynomial.eval₂_id]

end Commons.Algebra.MvPolynomial