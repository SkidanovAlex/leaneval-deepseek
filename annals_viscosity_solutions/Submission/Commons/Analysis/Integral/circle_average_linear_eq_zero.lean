import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Integral

theorem circle_average_linear_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (had : ∀ u v, F (u + v) = F u + F v) (hsm : ∀ c u, F (c • u) = c * F u)
    (e f : E) :
    (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi),
      F (Real.cos θ • e + Real.sin θ • f) = 0 := by
  have hpt : ∀ θ : ℝ, F (Real.cos θ • e + Real.sin θ • f)
      = Real.cos θ * F e + Real.sin θ * F f := by
    intro θ
    simp only [had, hsm]
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hsplit : (∫ θ in (0:ℝ)..(2*Real.pi), (Real.cos θ * F e + Real.sin θ * F f))
      = (∫ θ in (0:ℝ)..(2*Real.pi), Real.cos θ * F e)
        + (∫ θ in (0:ℝ)..(2*Real.pi), Real.sin θ * F f) :=
    intervalIntegral.integral_add
      ((Real.continuous_cos.mul continuous_const).intervalIntegrable _ _)
      ((Real.continuous_sin.mul continuous_const).intervalIntegrable _ _)
  rw [hsplit]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  rw [integral_cos, integral_sin]
  simp

end Commons.Analysis.Integral