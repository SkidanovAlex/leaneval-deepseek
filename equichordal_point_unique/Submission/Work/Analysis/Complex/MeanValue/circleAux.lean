import Mathlib

/-!
# Auxiliary lemmas for the area mean value inequality

Two elementary facts used by `norm_sq_mul_le_integral_ball`: the parametrised circle is
`2π`-periodic, and the integral of a `2π`-periodic function over `Ioo (-π) π` equals its integral
over `Ioc 0 (2π)` (the angle ranges of `Complex.polarCoord.target` and of `Real.circleAverage`).
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.MeanValue

/-- The parametrised circle `θ ↦ c + r * exp (θ I)` is `2π`-periodic. -/
theorem periodic_circle (u : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (fun θ : ℝ => ‖u (c + r * Complex.exp (θ * Complex.I))‖ ^ 2)
      (2 * Real.pi) := by
  intro θ
  have h : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [show (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
        = ((2 * (Real.pi : ℂ)) * Complex.I) + (θ : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  simp only [h]

/-- **The two angle ranges.**  A `2π`-periodic function has the same integral over `Ioo (-π) π`
(the angular fibre of `Complex.polarCoord.target`) and over `Ioc 0 (2π)` (the range of the circle
average). -/
theorem integral_Ioo_neg_pi_pi_eq_Ioc {f : ℝ → ℝ} (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f θ = ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), f θ := by
  have h1 : ∫ θ in Set.Ioo (-Real.pi) Real.pi, f θ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, f θ :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  rw [h1, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : (-Real.pi : ℝ) ≤ Real.pi),
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * Real.pi)]
  have h := hf.intervalIntegral_add_eq (-Real.pi) 0
  rwa [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring, zero_add] at h

end Work.Analysis.Complex.MeanValue
