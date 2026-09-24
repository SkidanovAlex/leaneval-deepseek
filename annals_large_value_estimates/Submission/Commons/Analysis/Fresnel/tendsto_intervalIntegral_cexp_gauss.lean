import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Commons.Analysis.Fresnel

open Complex MeasureTheory

open scoped Topology

set_option autoImplicit false

/-- Continuity at `ε = 0⁺` of the regularised Fresnel integral `∫_0^U exp(-(ε + i l) u²) du`. -/
theorem tendsto_intervalIntegral_cexp_gauss (l U : ℝ) (hl : 0 < l) (hU : 0 < U) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ u in (0:ℝ)..U, Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2))
      (𝓝[>] 0)
      (𝓝 (∫ u in (0:ℝ)..U, Complex.exp (-(((l : ℂ) * Complex.I)) * (u : ℂ)^2))) := by
  have hcont : Continuous
      (fun ε : ℝ => ∫ u in (0:ℝ)..U, Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (ε : ℝ) (u : ℝ) => Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2))
      (by fun_prop) 0 U
  have h0 : (fun ε : ℝ => ∫ u in (0:ℝ)..U, Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2)) 0
      = ∫ u in (0:ℝ)..U, Complex.exp (-(((l : ℂ) * Complex.I)) * (u : ℂ)^2) := by
    rw [show (fun ε : ℝ => ∫ u in (0:ℝ)..U, Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2)) 0
        = ∫ u in (0:ℝ)..U, Complex.exp (-(((0 : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2) from rfl]
    exact intervalIntegral.integral_congr (fun u hu => by simp)
  have htend : Filter.Tendsto
      (fun ε : ℝ => ∫ u in (0:ℝ)..U, Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2))
      (𝓝 0)
      (𝓝 (∫ u in (0:ℝ)..U, Complex.exp (-(((l : ℂ) * Complex.I)) * (u : ℂ)^2))) := by
    simpa only [h0] using hcont.tendsto 0
  exact htend.mono_left nhdsWithin_le_nhds

end Commons.Analysis.Fresnel