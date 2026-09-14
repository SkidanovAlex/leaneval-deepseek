import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.index_properties_pos_vanishing

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- **Chain rule for a translation (single variable).**  Substituting `X i ↦ X i + α i`
into a polynomial `P` and then differentiating coincides with differentiating `P` and
then shifting.  Stated for the underlying `aeval` substitution. -/
lemma aeval_shift_pderiv {K : Type*} [CommSemiring K] {σ : Type*}
    (α : σ → K) (i : σ) (P : MvPolynomial σ K) :
    MvPolynomial.aeval (fun j => MvPolynomial.C (α j) + MvPolynomial.X j)
        (MvPolynomial.pderiv i P) =
      MvPolynomial.pderiv i
        (MvPolynomial.aeval (fun j => MvPolynomial.C (α j) + MvPolynomial.X j) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      rw [MvPolynomial.pderiv_mul]
      simp only [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp]
      congr 1
      by_cases hn : n = i
      · subst hn; simp
      · simp [Pi.single_eq_of_ne hn]

/-- **Chain rule for a translation (single variable).**  The Taylor shift `X i ↦ X i + α i`
commutes with a single partial derivative. -/
lemma indexTay_pderiv {K : Type*} [CommSemiring K] {σ : Type*}
    (α : σ → K) (i : σ) (P : MvPolynomial σ K) :
    indexTay α (MvPolynomial.pderiv i P) = MvPolynomial.pderiv i (indexTay α P) := by
  simpa only [indexTay] using aeval_shift_pderiv α i P

/-- The Taylor shift `X i ↦ X i + α i` commutes with iterated partial derivatives
(the chain rule for a translation). -/
theorem indexTay_pderivIter {K : Type*} [CommSemiring K] {σ : Type*} [Fintype σ]
    (α : σ → K) (m : σ →₀ ℕ) (P : MvPolynomial σ K) :
    indexTay α (pderivIter m P) = pderivIter m (indexTay α P) := by
  -- Adding one more derivative to `m` preserves the statement.
  have hstep : ∀ (i : σ) (m : σ →₀ ℕ) (P : MvPolynomial σ K),
      indexTay α (pderivIter m P) = pderivIter m (indexTay α P) →
      indexTay α (pderivIter (m + Finsupp.single i 1) P) =
        pderivIter (m + Finsupp.single i 1) (indexTay α P) := by
    intro i m P h
    rw [← pderivIter_properties.2.2.1 i m P, indexTay_pderiv α i (pderivIter m P), h,
      pderivIter_properties.2.2.1 i m (indexTay α P)]
  -- Consequently adding `single a b` for any `b` preserves the statement.
  have hgen : ∀ (f : σ →₀ ℕ) (a : σ) (b : ℕ),
      (∀ P, indexTay α (pderivIter f P) = pderivIter f (indexTay α P)) →
      ∀ P, indexTay α (pderivIter (f + Finsupp.single a b) P) =
        pderivIter (f + Finsupp.single a b) (indexTay α P) := by
    intro f a b
    induction b with
    | zero => intro hf P; simpa using hf P
    | succ b ih =>
        intro hf P
        rw [Finsupp.single_add, ← add_assoc]
        exact hstep a (f + Finsupp.single a b) P (ih hf P)
  refine Finsupp.induction₂ (motive := fun m =>
    ∀ P, indexTay α (pderivIter m P) = pderivIter m (indexTay α P)) m ?_ ?_ P
  · intro P
    rw [pderivIter_properties.1 P, pderivIter_properties.1 (indexTay α P)]
  · intro a b f _ _ hf
    exact hgen f a b hf

end Commons.Algebra.MvPolynomial
