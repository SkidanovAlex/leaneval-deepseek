import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- The scalar multiple `n • single i 1` of the multi-index `single i 1` is the multi-index
`single i n`. -/
lemma nsmul_single_one_eq_single {σ : Type*} (i : σ) (n : ℕ) :
    n • (Finsupp.single i 1 : σ →₀ ℕ) = Finsupp.single i n := by
  induction n with
  | zero => rw [zero_nsmul, Finsupp.single_zero]
  | succ n ih => rw [succ_nsmul, ih]; exact (Finsupp.single_add i n 1).symm

/-- The partial derivative with respect to the unique variable corresponds, under
`MvPolynomial.uniqueAlgEquiv`, to the univariate formal derivative. -/
lemma uniqueAlgEquiv_pderiv_default {σ : Type*} [Unique σ] (P : MvPolynomial σ ℚ) :
    MvPolynomial.uniqueAlgEquiv ℚ σ (MvPolynomial.pderiv (default : σ) P) =
      Polynomial.derivative (MvPolynomial.uniqueAlgEquiv ℚ σ P) := by
  apply Polynomial.ext
  intro k
  rw [MvPolynomial.coeff_uniqueAlgEquiv, Polynomial.coeff_derivative,
      MvPolynomial.coeff_uniqueAlgEquiv]
  rw [← (pderivIter_properties (R := ℚ) (σ := σ)).2.1 (default : σ) P]
  rw [coeff_pderivIter]
  rw [← Finsupp.single_add, Fintype.prod_unique, Finsupp.single_eq_same,
      Finsupp.single_eq_same, Nat.descFactorial_one]
  push_cast
  ring

/-- The iterated partial derivative `∂^m` with `m = n • single default 1` is the `n`-fold
iterate of the partial derivative in the unique variable. -/
lemma pderivIter_nsmul_single {σ : Type*} [Unique σ] [Fintype σ] (n : ℕ)
    (P : MvPolynomial σ ℚ) :
    pderivIter (n • (Finsupp.single (default : σ) 1)) P =
      (MvPolynomial.pderiv (default : σ))^[n] P := by
  induction n with
  | zero =>
      rw [zero_nsmul, Function.iterate_zero_apply]
      exact (pderivIter_properties (R := ℚ) (σ := σ)).1 P
  | succ n ih =>
      have hprop := (pderivIter_properties (R := ℚ) (σ := σ)).2.2.1
      rw [succ_nsmul, Function.iterate_succ_apply']
      rw [← hprop (default : σ) (n • Finsupp.single (default : σ) 1) P, ih]

/-- `MvPolynomial.uniqueAlgEquiv` intertwines iterated partial differentiation in the unique
variable with iterated univariate formal differentiation. -/
lemma uniqueAlgEquiv_pderiv_iterate {σ : Type*} [Unique σ] [Fintype σ] (n : ℕ)
    (P : MvPolynomial σ ℚ) :
    MvPolynomial.uniqueAlgEquiv ℚ σ ((MvPolynomial.pderiv (default : σ))^[n] P) =
      (Polynomial.derivative^[n]) (MvPolynomial.uniqueAlgEquiv ℚ σ P) := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          uniqueAlgEquiv_pderiv_default, ih]

theorem uniqueAlgEquiv_pderivIter {σ : Type*} [Unique σ] [Fintype σ] (n : ℕ)
    (P : MvPolynomial σ ℚ) :
    MvPolynomial.uniqueAlgEquiv ℚ σ
        (Commons.Algebra.MvPolynomial.pderivIter (n • Finsupp.single (default : σ) 1) P) =
      (Polynomial.derivative^[n]) (MvPolynomial.uniqueAlgEquiv ℚ σ P) := by
  rw [pderivIter_nsmul_single n P]
  exact uniqueAlgEquiv_pderiv_iterate n P

end Commons.Algebra.MvPolynomial
