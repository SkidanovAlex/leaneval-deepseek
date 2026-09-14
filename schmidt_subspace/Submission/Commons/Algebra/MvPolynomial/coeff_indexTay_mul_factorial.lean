import Mathlib
import Submission.Commons.Algebra.MvPolynomial.index_properties_pos_vanishing
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.Algebra.MvPolynomial.indexTay_pderivIter

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- **Multivariate Taylor coefficient formula.**  For a polynomial `P` over a field `K`, an
evaluation point `α` and a multi-index `m`, the `m`-th coefficient of the Taylor shift
`indexTay α P = P(X + α)` equals `(∂^m P)(α)` divided by `m! = ∏ i, (m i)!`.

Proof: both sides are `K`-linear in `P`, so it suffices to check a monomial
`P = monomial s c`, where `indexTay α P` has `m`-th coefficient
`c * ∏ i, (s i).choose (m i) * α i ^ (s i - m i)` and `∂^m P` evaluated at `α` is
`c * ∏ i, (s i).descFactorial (m i) * α i ^ (s i - m i)`, while
`(m i)! * (s i).choose (m i) = (s i).descFactorial (m i)`. -/
theorem coeff_indexTay_mul_factorial {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (α : σ → K) (m : σ →₀ ℕ) (P : MvPolynomial σ K) :
    ((∏ i : σ, (m i).factorial) : K) *
        (Commons.Algebra.MvPolynomial.indexTay α P).coeff m =
      MvPolynomial.eval α (Commons.Algebra.MvPolynomial.pderivIter m P) := by
  classical
  revert P
  refine Finsupp.induction₂
    (motive := fun m => ∀ P : MvPolynomial σ K,
      ((∏ i : σ, (m i).factorial) : K) *
          (Commons.Algebra.MvPolynomial.indexTay α P).coeff m =
        MvPolynomial.eval α (Commons.Algebra.MvPolynomial.pderivIter m P)) m ?_ ?_
  · intro P
    have hfac0 : (∏ i : σ, (((0 : σ →₀ ℕ) i).factorial : K)) = 1 := by simp
    rw [hfac0, one_mul, (pderivIter_properties (R := K) (σ := σ)).1 P]
    rw [← MvPolynomial.constantCoeff_eq, constantCoeff_indexTay]
  · intro a b f _ha _hb ih P
    -- the factorial identity, pointwise on the coordinates
    have hpoint : ∀ i : σ, ((f + Finsupp.single a b) i).factorial
        = (f i).factorial * ((f + Finsupp.single a b) i).descFactorial
            ((Finsupp.single a b) i) := by
      intro i
      by_cases hi : i = a
      · subst hi
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        have hfb := Nat.factorial_mul_descFactorial (n := f i + b) (k := b) (by omega)
        rw [Nat.add_sub_cancel] at hfb
        exact hfb.symm
      · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hi, add_zero,
          Nat.descFactorial_zero, mul_one]
    have hcast : (∏ i : σ, (((f + Finsupp.single a b) i).factorial : K))
        = (∏ i : σ, ((f i).factorial : K)) *
          ((∏ i : σ, ((f + Finsupp.single a b) i).descFactorial
            ((Finsupp.single a b) i) : ℕ) : K) := by
      rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [hpoint i, Nat.cast_mul])
    have hIH := ih (Commons.Algebra.MvPolynomial.pderivIter (Finsupp.single a b) P)
    rw [indexTay_pderivIter α (Finsupp.single a b) P] at hIH
    rw [← pderivIter_add (Finsupp.single a b) f P] at hIH
    rw [add_comm (Finsupp.single a b) f] at hIH
    rw [coeff_pderivIter (Finsupp.single a b) f (Commons.Algebra.MvPolynomial.indexTay α P)]
      at hIH
    rw [hcast]
    calc (((∏ i : σ, (f i).factorial : K)) *
            ((∏ i : σ, ((f + Finsupp.single a b) i).descFactorial
              ((Finsupp.single a b) i) : ℕ) : K)) *
            MvPolynomial.coeff (f + Finsupp.single a b)
              (Commons.Algebra.MvPolynomial.indexTay α P)
        = ((∏ i : σ, (f i).factorial : K)) *
            (MvPolynomial.coeff (f + Finsupp.single a b)
                (Commons.Algebra.MvPolynomial.indexTay α P) *
              ((∏ i : σ, ((f + Finsupp.single a b) i).descFactorial
                ((Finsupp.single a b) i) : ℕ) : K)) := by ring
      _ = MvPolynomial.eval α
            (Commons.Algebra.MvPolynomial.pderivIter (f + Finsupp.single a b) P) := hIH

end Commons.Algebra.MvPolynomial
