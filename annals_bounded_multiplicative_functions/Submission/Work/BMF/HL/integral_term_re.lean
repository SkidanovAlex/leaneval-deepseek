import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

/-- Integrating one term of the frequency-averaged sum over `θ ∈ [0,δ]`: the real part, the
division by the real constant `p`, the constant factor `g p` and the interval integral can all be
pulled apart, giving `(g p · ∫_0^δ p^{-i(u+θ)} dθ).re / p`. -/
theorem integral_term_re (g : ℕ → ℂ) (p : ℕ) (hp : 2 ≤ p) (u : ℝ) (δ : ℝ) :
    ∫ θ in (0 : ℝ)..δ, (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re / (p : ℝ)
      = ((g p) * (∫ θ in (0 : ℝ)..δ, (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ))))).re
          / (p : ℝ) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hNe : NeZero (p : ℂ) := ⟨hp0⟩
  have hF : Continuous fun θ : ℝ => (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ))) := by
    have h1 : Continuous fun θ : ℝ => -(Complex.I * ((u + θ : ℝ) : ℂ)) := by continuity
    exact (continuous_const_cpow (p : ℂ)).comp h1
  have hint : IntervalIntegrable
      (fun θ : ℝ => g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))) MeasureTheory.volume 0 δ :=
    (continuous_const.mul hF).intervalIntegrable 0 δ
  -- the real part of the interval integral is the integral of the real part
  have hre_lem : (∫ θ in (0 : ℝ)..δ,
        Complex.reCLM (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))))
      = Complex.reCLM (∫ θ in (0 : ℝ)..δ,
          g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))) :=
    ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
  have h2 : (∫ θ in (0 : ℝ)..δ, (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re)
      = (∫ θ in (0 : ℝ)..δ, g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re := by
    simpa only [Complex.reCLM_apply] using hre_lem
  rw [intervalIntegral.integral_div, h2, intervalIntegral.integral_const_mul]

end Work.BMF.HL
