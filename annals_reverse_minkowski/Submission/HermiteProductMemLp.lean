import Mathlib
import Submission.MvPolyMemLp

namespace Commons.Analysis.GaussianMeasure

open Polynomial MvPolynomial

/-- Evaluating, at `x`, the multivariate polynomial obtained by substituting the `i`-th variable
for the single variable of a univariate real polynomial gives the univariate evaluation at `x i`. -/
private lemma eval_aeval_X_herm {N : ℕ} (x : Fin N → ℝ) (i : Fin N) (p : Polynomial ℝ) :
    MvPolynomial.eval x
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) p)
      = Polynomial.aeval (x i) p := by
  have h := Polynomial.aeval_algHom_apply (R := ℝ) (MvPolynomial.aeval x)
    (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) p
  rw [MvPolynomial.aeval_X] at h
  simpa using h.symm

/-- Coercing an integer Hermite polynomial to a real polynomial does not change its evaluation. -/
private lemma aeval_hermite_map (a : ℝ) (k : ℕ) :
    Polynomial.aeval a (Polynomial.hermite k)
      = Polynomial.aeval a ((Polynomial.hermite k).map (Int.castRingHom ℝ)) :=
  Polynomial.aeval_eq_aeval_map (S := ℝ) (T := ℝ) (φ := Int.castRingHom ℝ)
    (Subsingleton.elim _ _) (Polynomial.hermite k) a

theorem memLp_hermite_product {N : ℕ} (α : Fin N → ℕ) :
    MeasureTheory.MemLp (fun x : EuclideanSpace ℝ (Fin N) =>
      ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))) 2
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) := by
  -- Package the product of Hermite factors as a single multivariate polynomial.
  set P : MvPolynomial (Fin N) ℝ :=
    ∏ i, Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin N) ℝ)
      ((Polynomial.hermite (α i)).map (Int.castRingHom ℝ)) with hP
  have hfun : (fun x : EuclideanSpace ℝ (Fin N) =>
        ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i)))
      = fun x : EuclideanSpace ℝ (Fin N) =>
        MvPolynomial.eval (fun i => x.ofLp i) P := by
    funext x
    rw [hP, MvPolynomial.eval_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [eval_aeval_X_herm]
    exact aeval_hermite_map (x.ofLp i) (α i)
  rw [hfun]
  exact memLp_mvpoly_withDensity_exp_neg_sq_half P

end Commons.Analysis.GaussianMeasure
