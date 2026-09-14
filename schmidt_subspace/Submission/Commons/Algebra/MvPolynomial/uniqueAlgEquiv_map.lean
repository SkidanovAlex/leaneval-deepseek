import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Algebra.MvPolynomial

theorem uniqueAlgEquiv_map {σ : Type*} [Unique σ] (P : MvPolynomial σ ℤ) :
    (MvPolynomial.uniqueAlgEquiv ℤ σ P).map (Int.castRingHom ℚ) =
      MvPolynomial.uniqueAlgEquiv ℚ σ (P.map (Int.castRingHom ℚ)) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
      rw [MvPolynomial.uniqueAlgEquiv_monomial, Polynomial.map_monomial,
        MvPolynomial.map_monomial, MvPolynomial.uniqueAlgEquiv_monomial]
  | add P Q hP hQ =>
      rw [map_add, Polynomial.map_add, map_add, hP, hQ, map_add]

end Commons.Algebra.MvPolynomial