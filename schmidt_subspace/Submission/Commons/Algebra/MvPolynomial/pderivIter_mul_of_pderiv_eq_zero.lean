import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add

namespace Commons.Algebra.MvPolynomial

/-- One-variable version of the product rule for an iterated derivative: if `∂_i Q = 0` then
`∂^{b·e_i}(A * Q) = (∂^{b·e_i} A) * Q`. -/
lemma pderivIter_single_mul_of_pderiv_eq_zero {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (i : σ) (b : ℕ) (A Q : MvPolynomial σ R) (hQ : MvPolynomial.pderiv i Q = 0) :
    pderivIter (Finsupp.single i b) (A * Q) = pderivIter (Finsupp.single i b) A * Q := by
  induction b with
  | zero =>
      rw [Finsupp.single_zero, pderivIter_properties.1, pderivIter_properties.1]
  | succ b ih =>
      rw [Finsupp.single_add, pderivIter_single_add 1 i (Finsupp.single i b) (A * Q), ih,
        pderivIter_properties.2.1, MvPolynomial.pderiv_mul, hQ, mul_zero, add_zero,
        pderivIter_properties.2.2.1, pderivIter_single_add 1 i (Finsupp.single i b) A]

theorem pderivIter_mul_of_pderiv_eq_zero {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) (P Q : MvPolynomial σ R)
    (hQ : ∀ i ∈ m.support, MvPolynomial.pderiv i Q = 0) :
    Commons.Algebra.MvPolynomial.pderivIter m (P * Q) =
      Commons.Algebra.MvPolynomial.pderivIter m P * Q := by
  classical
  revert P Q
  refine Finsupp.induction₂ m ?_ ?_
  · intro P Q _
    rw [pderivIter_properties.1, pderivIter_properties.1]
  · intro a b f ha hb ih P Q hQ
    have hsub : f.support ⊆ (f + Finsupp.single a b).support :=
      Finsupp.support_mono (le_add_right (le_refl f))
    have hQf : ∀ i ∈ f.support, MvPolynomial.pderiv i Q = 0 :=
      fun i hi => hQ i (hsub hi)
    have haQ : MvPolynomial.pderiv a Q = 0 := by
      apply hQ a
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp ha, zero_add]
      exact hb
    rw [pderivIter_add f (Finsupp.single a b) (P * Q), ih P Q hQf,
      pderivIter_single_mul_of_pderiv_eq_zero a b (pderivIter f P) Q haQ,
      ← pderivIter_add f (Finsupp.single a b) P]

end Commons.Algebra.MvPolynomial
