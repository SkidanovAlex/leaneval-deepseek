import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add

namespace Commons.Algebra.MvPolynomial

lemma pderivIter_rename {σ τ : Type*} [Fintype σ] [Fintype τ] {R : Type*} [CommSemiring R]
    (e : σ → τ) (he : Function.Injective e) (m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    Commons.Algebra.MvPolynomial.pderivIter (m.mapDomain e) (MvPolynomial.rename e P) =
      MvPolynomial.rename e (Commons.Algebra.MvPolynomial.pderivIter m P) := by
  classical
  have h0σ : ∀ Q : MvPolynomial σ R, pderivIter (0 : σ →₀ ℕ) Q = Q :=
    (pderivIter_properties (R := R) (σ := σ)).1
  have h0τ : ∀ Q : MvPolynomial τ R, pderivIter (0 : τ →₀ ℕ) Q = Q :=
    (pderivIter_properties (R := R) (σ := τ)).1
  have hsingle1 : ∀ (a : σ) (Q : MvPolynomial σ R),
      pderivIter (Finsupp.single (e a) 1) (MvPolynomial.rename e Q) =
        MvPolynomial.rename e (pderivIter (Finsupp.single a 1) Q) := by
    intro a Q
    rw [(pderivIter_properties (R := R) (σ := τ)).2.1 (e a) (MvPolynomial.rename e Q),
      (pderivIter_properties (R := R) (σ := σ)).2.1 a Q,
      MvPolynomial.pderiv_rename (f := e) he a Q]
  have hsingle : ∀ (a : σ) (b : ℕ) (Q : MvPolynomial σ R),
      pderivIter (Finsupp.single (e a) b) (MvPolynomial.rename e Q) =
        MvPolynomial.rename e (pderivIter (Finsupp.single a b) Q) := by
    intro a b
    induction b with
    | zero =>
        intro Q
        rw [Finsupp.single_zero, Finsupp.single_zero, h0τ, h0σ]
    | succ b ih =>
        intro Q
        rw [Finsupp.single_add, pderivIter_add, ih, hsingle1]
        rw [Finsupp.single_add, pderivIter_add]
  have key : ∀ (m : σ →₀ ℕ) (Q : MvPolynomial σ R),
      pderivIter (m.mapDomain e) (MvPolynomial.rename e Q) =
        MvPolynomial.rename e (pderivIter m Q) := by
    intro m
    refine Finsupp.induction m ?_ ?_
    · intro Q
      rw [Finsupp.mapDomain_zero, h0τ, h0σ]
    · intro a b f _hb _hf ih Q
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, pderivIter_add, hsingle a b Q,
        ih (pderivIter (Finsupp.single a b) Q), ← pderivIter_add]
  exact key m P

end Commons.Algebra.MvPolynomial
