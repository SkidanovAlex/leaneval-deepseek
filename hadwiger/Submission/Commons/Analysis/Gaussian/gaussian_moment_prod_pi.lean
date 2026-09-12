import Mathlib.MeasureTheory.Integral.Pi

namespace Commons.Analysis.Gaussian

lemma gaussian_moment_prod_pi {n : ℕ} (a : Fin n → ℕ) :
    (∫ x : Fin n → ℝ, ∏ i : Fin n, (x i) ^ (2 * a i) * Real.exp (-((x i) ^ 2))) =
      ∏ i : Fin n, (∫ t : ℝ, t ^ (2 * a i) * Real.exp (-(t ^ 2))) := by
  simpa using
    (MeasureTheory.integral_fintype_prod_volume_eq_prod
      (ι := Fin n) (E := fun _ : Fin n ↦ ℝ) (f := fun (i : Fin n) (t : ℝ) =>
        t ^ (2 * a i) * Real.exp (-(t ^ 2))))

end Commons.Analysis.Gaussian
