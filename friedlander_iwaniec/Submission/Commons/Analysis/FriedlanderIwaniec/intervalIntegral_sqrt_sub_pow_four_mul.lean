import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Commons.Analysis.FriedlanderIwaniec

lemma intervalIntegral_sqrt_sub_pow_four_mul {y : ℝ} (hy : 0 ≤ y) :
    ∫ t in (0)..y, Real.sqrt (y ^ 4 - t ^ 4) =
      (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 := by
  have hsub : (∫ u in (0:ℝ)..1, Real.sqrt (y ^ 4 - (y * u) ^ 4) * y)
      = ∫ t in (0:ℝ)..y, Real.sqrt (y ^ 4 - t ^ 4) := by
    have h := intervalIntegral.integral_comp_mul_deriv
      (a := (0:ℝ)) (b := 1) (f := fun u : ℝ => y * u) (f' := fun _ : ℝ => y)
      (g := fun t : ℝ => Real.sqrt (y ^ 4 - t ^ 4))
      (fun x _ => by simpa using (hasDerivAt_id x).const_mul y)
      continuousOn_const (by fun_prop)
    simpa using h
  rw [← hsub]
  have hpt : ∀ u : ℝ,
      Real.sqrt (y ^ 4 - (y * u) ^ 4) * y = y ^ 3 * Real.sqrt (1 - u ^ 4) := by
    intro u
    have h1 : y ^ 4 - (y * u) ^ 4 = y ^ 4 * (1 - u ^ 4) := by ring
    rw [h1, Real.sqrt_mul (pow_nonneg hy 4)]
    have h2 : Real.sqrt (y ^ 4) = y ^ 2 := by
      rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hy 2)]
    rw [h2]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  ring

end Commons.Analysis.FriedlanderIwaniec