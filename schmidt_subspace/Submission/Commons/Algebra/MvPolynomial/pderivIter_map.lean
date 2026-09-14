import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties

namespace Commons.Algebra.MvPolynomial

lemma pderivIter_map {σ : Type*} [Fintype σ] {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    Commons.Algebra.MvPolynomial.pderivIter m (P.map f) =
      (Commons.Algebra.MvPolynomial.pderivIter m P).map f := by
  have h0R : ∀ Q : MvPolynomial σ R, pderivIter (0 : σ →₀ ℕ) Q = Q :=
    (pderivIter_properties (R := R) (σ := σ)).1
  have h0S : ∀ Q : MvPolynomial σ S, pderivIter (0 : σ →₀ ℕ) Q = Q :=
    (pderivIter_properties (R := S) (σ := σ)).1
  have hderivR : ∀ (i : σ) (n : σ →₀ ℕ) (Q : MvPolynomial σ R),
      MvPolynomial.pderiv i (pderivIter n Q) = pderivIter (n + Finsupp.single i 1) Q :=
    (pderivIter_properties (R := R) (σ := σ)).2.2.1
  have hderivS : ∀ (i : σ) (n : σ →₀ ℕ) (Q : MvPolynomial σ S),
      MvPolynomial.pderiv i (pderivIter n Q) = pderivIter (n + Finsupp.single i 1) Q :=
    (pderivIter_properties (R := S) (σ := σ)).2.2.1
  refine Finsupp.induction m ?_ ?_
  · rw [h0S (P.map f), h0R P]
  · intro a b g _ha _hb ih
    have hstep : ∀ k : ℕ, pderivIter (g + Finsupp.single a k) (P.map f) =
        (pderivIter (g + Finsupp.single a k) P).map f := by
      intro k
      induction k with
      | zero => rw [Finsupp.single_zero, add_zero]; exact ih
      | succ k ihk =>
        rw [Finsupp.single_add, ← add_assoc,
          ← hderivS a (g + Finsupp.single a k) (P.map f), ihk,
          MvPolynomial.pderiv_map, hderivR a (g + Finsupp.single a k) P]
    rw [add_comm (Finsupp.single a b) g]
    exact hstep b

end Commons.Algebra.MvPolynomial
