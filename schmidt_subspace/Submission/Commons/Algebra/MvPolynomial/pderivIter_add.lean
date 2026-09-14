import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties

namespace Commons.Algebra.MvPolynomial

/-- A one-coordinate instance of additivity: `∂^{c + a·e_i} = ∂^{a·e_i} ∘ ∂^c`.  Proved by
induction on `a` from `pderiv i (∂^m P) = ∂^{m + e_i} P`. -/
theorem pderivIter_single_add {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (a : ℕ) (i : σ) (c : σ →₀ ℕ) (Q : MvPolynomial σ R) :
    pderivIter (c + Finsupp.single i a) Q =
      pderivIter (Finsupp.single i a) (pderivIter c Q) := by
  have h0 : ∀ P : MvPolynomial σ R, pderivIter (0 : σ →₀ ℕ) P = P :=
    (pderivIter_properties (R := R) (σ := σ)).1
  have hadd : ∀ (i : σ) (m : σ →₀ ℕ) (P : MvPolynomial σ R),
      MvPolynomial.pderiv i (pderivIter m P) = pderivIter (m + Finsupp.single i 1) P :=
    (pderivIter_properties (R := R) (σ := σ)).2.2.1
  induction a with
  | zero => simp [h0]
  | succ a ih =>
      rw [Finsupp.single_add, ← add_assoc, ← hadd i (c + Finsupp.single i a) Q, ih,
        hadd i (Finsupp.single i a) (pderivIter c Q)]

/-- `pderivIter` is additive in the multi-index: applying `∂^{m+m'}` is the same as first
applying `∂^m` and then `∂^{m'}`. -/
theorem pderivIter_add {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m m' : σ →₀ ℕ) (P : MvPolynomial σ R) :
    Commons.Algebra.MvPolynomial.pderivIter (m + m') P =
      Commons.Algebra.MvPolynomial.pderivIter m' (Commons.Algebra.MvPolynomial.pderivIter m P) := by
  have h0 : ∀ P : MvPolynomial σ R, pderivIter (0 : σ →₀ ℕ) P = P :=
    (pderivIter_properties (R := R) (σ := σ)).1
  refine Finsupp.induction m' ?_ ?_
  · rw [add_zero, h0]
  · intro a b f _ha _hb ih
    rw [add_comm (Finsupp.single a b) f, ← add_assoc,
      pderivIter_single_add b a (m + f) P, ih,
      pderivIter_single_add b a f (pderivIter m P)]

end Commons.Algebra.MvPolynomial
