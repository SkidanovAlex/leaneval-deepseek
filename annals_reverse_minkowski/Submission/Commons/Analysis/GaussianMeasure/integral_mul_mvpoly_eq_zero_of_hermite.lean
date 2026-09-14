import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.GaussianMeasure.hermite_multivariate_span

open MeasureTheory MvPolynomial
open scoped BigOperators ENNReal

noncomputable section

namespace Commons.Analysis.GaussianMeasure

private def hermR (k : ℕ) : Polynomial ℝ := (Polynomial.hermite k).map (Int.castRingHom ℝ)

private lemma aeval_hermR_real (a : ℝ) (k : ℕ) :
    Polynomial.aeval a (hermR k) = Polynomial.aeval a (Polynomial.hermite k) := by
  rw [hermR]
  exact (Polynomial.aeval_eq_aeval_map (R := ℤ) (T := ℝ)
    (Subsingleton.elim _ _) (Polynomial.hermite k) a).symm

private lemma eval_aeval_X_real {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (p : Polynomial ℝ) :
    MvPolynomial.eval x
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) p)
      = Polynomial.aeval (x i) p := by
  have h := Polynomial.aeval_algHom_apply (R := ℝ) (MvPolynomial.aeval x)
    (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) p
  rw [MvPolynomial.aeval_X] at h
  simpa using h.symm

private def hermPoly {m : ℕ} (β : Fin m → ℕ) : MvPolynomial (Fin m) ℝ :=
  ∏ i, Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) (hermR (β i))

private lemma eval_hermPoly {m : ℕ} (β : Fin m → ℕ) (x : Fin m → ℝ) :
    MvPolynomial.eval x (hermPoly β)
      = ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (β i)) := by
  unfold hermPoly
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_aeval_X_real, aeval_hermR_real]

private lemma integrable_mul_herm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hint : ∀ P : MvPolynomial (Fin n) ℝ, MeasureTheory.Integrable
      (fun x => f x * MvPolynomial.eval (fun i => x.ofLp i) P)
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))))
    (β : Fin n → ℕ) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        f x * ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (β i)))
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) := by
  have h := hint (hermPoly β)
  rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
        f x * MvPolynomial.eval (fun i => x.ofLp i) (hermPoly β))
      = (fun x : EuclideanSpace ℝ (Fin n) =>
        f x * ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (β i))) from by
    funext x
    rw [eval_hermPoly]] at h
  exact h

theorem integral_mul_mvpoly_eq_zero_of_hermite {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hint : ∀ P : MvPolynomial (Fin n) ℝ, MeasureTheory.Integrable
      (fun x => f x * MvPolynomial.eval (fun i => x.ofLp i) P)
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))))
    (h : ∀ α : Fin n → ℕ, ∫ x, f x * (∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i)))
      ∂(MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) = 0) :
    ∀ P : MvPolynomial (Fin n) ℝ, ∫ x, f x * MvPolynomial.eval (fun i => x.ofLp i) P
      ∂(MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) = 0 := by
  intro P
  obtain ⟨c, hc⟩ := hermite_multivariate_span (m := n) (d := P.totalDegree)
    (fun y : Fin n → ℝ => MvPolynomial.eval y P) ⟨P, fun y => rfl, le_rfl⟩
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    MeasureTheory.volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2))) with hμ
  have key : ∀ x : EuclideanSpace ℝ (Fin n),
      f x * MvPolynomial.eval (fun i => x.ofLp i) P
        = ∑ α : Fin n → Fin (P.totalDegree + 1),
            c α * (f x * ∏ i,
              Polynomial.aeval (x.ofLp i) (Polynomial.hermite ((α i : ℕ)))) := by
    intro x
    rw [hc (fun i => x.ofLp i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  have hintG : ∀ α : Fin n → Fin (P.totalDegree + 1),
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          f x * ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite ((α i : ℕ)))) μ := by
    intro α
    rw [hμ]
    exact integrable_mul_herm f hint (fun i => (α i : ℕ))
  have hint_int : ∀ α : Fin n → Fin (P.totalDegree + 1),
      ∫ x, f x * ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite ((α i : ℕ))) ∂μ = 0 := by
    intro α
    have hh := h (fun i => (α i : ℕ))
    rw [hμ]
    exact hh
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun α _ => (hintG α).const_mul (c α))]
  rw [Finset.sum_congr rfl (fun α _ => MeasureTheory.integral_const_mul (c α) _)]
  rw [Finset.sum_congr rfl (fun α _ => by rw [hint_int α])]
  simp

end Commons.Analysis.GaussianMeasure