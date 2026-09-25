import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat

open MeasureTheory

/-- **Integration by parts for the flat `∂̄`-operator on `ℂⁿ`.**
For `C¹` functions `u`, `v : ℂⁿ → ℂ` such that all the products appearing are integrable,
`∫ x, u x * ∂̄_k v x = -∫ x, ∂̄_k u x * v x`, where `∂̄_k = dbarCoord k` is the flat `∂̄`-operator
of `Submission.Work.CR.Flat.Polydisc` (`dbarCoord j u z = (1/2)(∂_{x_j} + i ∂_{y_j})u(z)`).
It is stated in namespace `Work.CR.Flat`.

Proof: expand the definition
`dbarCoord k w x = (1/2) * (fderiv ℝ w x (Pi.single k 1) + Complex.I * fderiv ℝ w x (Pi.single k Complex.I))`,
integrate termwise, and apply Mathlib's one-dimensional integration by parts
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
(`Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts`) twice, once in each of the two
directions `Pi.single k 1` and `Pi.single k Complex.I`, using `FiniteDimensional ℝ (Fin n → ℂ)`
and `IsAddHaarMeasure volume`. -/
theorem integral_mul_dbarCoord_eq_neg {n : ℕ} (k : Fin n) {u v : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (h1u : MeasureTheory.Integrable (fun x => fderiv ℝ u x (Pi.single k 1) * v x) MeasureTheory.volume)
    (hIu : MeasureTheory.Integrable (fun x => fderiv ℝ u x (Pi.single k Complex.I) * v x) MeasureTheory.volume)
    (h1v : MeasureTheory.Integrable (fun x => u x * fderiv ℝ v x (Pi.single k 1)) MeasureTheory.volume)
    (hIv : MeasureTheory.Integrable (fun x => u x * fderiv ℝ v x (Pi.single k Complex.I)) MeasureTheory.volume)
    (huv : MeasureTheory.Integrable (fun x => u x * v x) MeasureTheory.volume) :
    ∫ x, u x * dbarCoord k v x = -∫ x, dbarCoord k u x * v x := by
  -- Both `u` and `v` are differentiable everywhere, hence on the relevant supports.
  have hudiff : ∀ x ∈ tsupport v, DifferentiableAt ℝ u x := fun x _ =>
    (hu.differentiable (by norm_num)).differentiableAt
  have hvdiff : ∀ x ∈ tsupport u, DifferentiableAt ℝ v x := fun x _ =>
    (hv.differentiable (by norm_num)).differentiableAt
  -- One-dimensional integration by parts in the real direction `Pi.single k 1`.
  have hIBP1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := v) (v := Pi.single k (1 : ℂ)) h1u h1v huv hudiff hvdiff
  -- One-dimensional integration by parts in the direction `Pi.single k Complex.I`.
  have hIBPI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := v) (v := Pi.single k Complex.I) hIu hIv huv hudiff hvdiff
  -- Expand `∂̄_k v` in the left integrand.
  have hcongr1 : (fun x => u x * dbarCoord k v x)
      = fun x => (1 / 2 : ℂ) * (u x * fderiv ℝ v x (Pi.single k 1))
          + (1 / 2 * Complex.I) * (u x * fderiv ℝ v x (Pi.single k Complex.I)) := by
    funext x; simp only [dbarCoord]; ring
  have hL : ∫ x, u x * dbarCoord k v x
      = (1 / 2 : ℂ) * (∫ x, u x * fderiv ℝ v x (Pi.single k 1))
        + (1 / 2 * Complex.I) * (∫ x, u x * fderiv ℝ v x (Pi.single k Complex.I)) := by
    rw [hcongr1, integral_add (h1v.const_mul _) (hIv.const_mul _), integral_const_mul,
      integral_const_mul]
  -- Expand `∂̄_k u` in the right integrand.
  have hcongr2 : (fun x => dbarCoord k u x * v x)
      = fun x => (1 / 2 : ℂ) * (fderiv ℝ u x (Pi.single k 1) * v x)
          + (1 / 2 * Complex.I) * (fderiv ℝ u x (Pi.single k Complex.I) * v x) := by
    funext x; simp only [dbarCoord]; ring
  have hR : ∫ x, dbarCoord k u x * v x
      = (1 / 2 : ℂ) * (∫ x, fderiv ℝ u x (Pi.single k 1) * v x)
        + (1 / 2 * Complex.I) * (∫ x, fderiv ℝ u x (Pi.single k Complex.I) * v x) := by
    rw [hcongr2, integral_add (h1u.const_mul _) (hIu.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hL, hR, hIBP1, hIBPI]
  ring

end Work.CR.Flat
