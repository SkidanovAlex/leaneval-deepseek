import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.integral_radial
import Submission.Work.FTS.PressureOn.PoissonAux.integral_mul_deriv_deriv_rhoProfile

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux.KI

/-- **The total mass of the truncation kernel `massKernel 1` is `-1`.**

`massKernel 1 x = (4π‖x‖)⁻¹ ρ''(‖x‖)` with `ρ = rhoProfile 1`, so it is the radially symmetric
function `g ‖x‖`, `g r = (4πr)⁻¹ ρ''(r)`.  The radial change of variables `integral_radial` turns
the integral into `4π ∫_0^∞ r² g(r) dr = ∫_0^∞ r ρ''(r) dr` (for `r > 0`), and the one-dimensional
identity `integral_mul_deriv_deriv_rhoProfile` gives `∫_0^∞ r ρ''(r) dr = -1`. -/
theorem massKernel_one_mass : ∫ x : R3, massKernel 1 x = -1 := by
  set f : ℝ → ℝ := fun r => deriv (deriv (rhoProfile 1)) r with hf
  set g : ℝ → ℝ := fun r => (4 * Real.pi * r)⁻¹ * f r with hg
  -- the kernel is the radially symmetric function `x ↦ g ‖x‖`
  have hfun : (fun x : R3 => massKernel 1 x) = fun x : R3 => g ‖x‖ := by
    funext x
    simp only [massKernel_eq, newtonKernel, hg, hf]
  rw [hfun, integral_radial g]
  -- the radial integrand reduces to `(4π)⁻¹ r ρ''(r)` for `r > 0`
  have h1 : ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r
      = (4 * Real.pi)⁻¹ * ∫ r in Set.Ioi (0 : ℝ), r * f r := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [hg]
    rw [mul_inv]
    have hrr : r ^ 2 * r⁻¹ = r := by
      rw [sq, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
    rw [show r ^ 2 * ((4 * Real.pi)⁻¹ * r⁻¹ * f r)
          = (4 * Real.pi)⁻¹ * ((r ^ 2 * r⁻¹) * f r) from by ring, hrr]
  rw [h1, hf, integral_mul_deriv_deriv_rhoProfile 1 (by norm_num)]
  -- `4π · ((4π)⁻¹ · (-1)) = -1`
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

end Work.FTS.PressureOn.PoissonAux.KI
