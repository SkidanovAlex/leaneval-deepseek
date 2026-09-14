import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- Pointwise identity: the `n`-dimensional Gaussian (as `exp (-c * ∑ (x i)²)`) is the product
over the coordinates of the one-dimensional Gaussians `exp (-c * (x i)²)`. -/
private lemma gaussian_pointwise_eq (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    (∏ i : Fin n, Real.exp (-c * (x i) ^ 2)) = Real.exp (-c * (∑ i : Fin n, (x i) ^ 2)) := by
  rw [← Real.exp_sum (Finset.univ : Finset (Fin n))]
  congr 1
  rw [Finset.mul_sum]

/-- The product over `n` independent one-dimensional Gaussians is integrable w.r.t. the finite
product (pi) measure. This is `MeasureTheory.Integrable.fintype_prod` applied to
`integrable_exp_neg_mul_sq`. -/
private lemma gaussian_prod_integrable_pi (n : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable
      (fun x : Fin n → ℝ => ∏ i : Fin n, Real.exp (-c * (x i) ^ 2))
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  exact (Integrable.fintype_prod (ι := Fin n) (E := ℝ) (𝕜 := ℝ)
      (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun (_ : Fin n) (t : ℝ) => Real.exp (-c * t ^ 2))
      (fun _ => integrable_exp_neg_mul_sq hc))

theorem gaussian_integrable_fn (n : ℕ) (c : ℝ) (hc : 0 < c) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => Real.exp (-c * (∑ i : Fin n, (x i) ^ 2))) := by
  -- The volume on the function space `Fin n → ℝ` is the finite product (pi) measure.
  rw [MeasureTheory.volume_pi]
  -- Reduce to the (already integrable) product of the one-dimensional Gaussians.
  exact Integrable.congr (gaussian_prod_integrable_pi n c hc)
    (ae_of_all _ (fun x => gaussian_pointwise_eq n c x))

end Commons.Analysis.Fourier