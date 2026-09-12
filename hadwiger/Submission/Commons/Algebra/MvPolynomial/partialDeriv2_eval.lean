import Mathlib
import Submission.Commons.Algebra.MvPolynomial.gradient_eval

noncomputable section

open scoped Gradient
open InnerProductSpace

namespace Commons.Algebra.MvPolynomial

/-- The directional derivative of a polynomial function in the coordinate direction `i`
is the polynomial obtained by applying the `i`-th partial derivative. -/
private lemma fderiv_eval_single {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => y j) Q) x
        (EuclideanSpace.single i (1:ℝ))
      = MvPolynomial.eval (fun j => x j) (MvPolynomial.pderiv i Q) := by
  rw [← inner_gradient_left]
  rw [gradient_eval]
  rw [sum_inner]
  rw [Finset.sum_eq_single i]
  · rw [inner_smul_left, EuclideanSpace.inner_single_left]
    simp
  · intro k _ hk
    rw [inner_smul_left, EuclideanSpace.inner_single_left]
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem partialDeriv2_eval
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => z j) P) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))
      = MvPolynomial.eval (fun j => x j)
          (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) := by
  have hfun : ∀ i : Fin n, (fun y : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => z j) P) y
          (EuclideanSpace.single i 1))
      = fun y => MvPolynomial.eval (fun j => y j) (MvPolynomial.pderiv i P) :=
    fun i => funext (fun y => fderiv_eval_single P y i)
  rw [Finset.sum_congr rfl (fun i _ => by rw [hfun i])]
  rw [Finset.sum_congr rfl (fun i _ => fderiv_eval_single (MvPolynomial.pderiv i P) x i)]
  rw [map_sum]

end Commons.Algebra.MvPolynomial
