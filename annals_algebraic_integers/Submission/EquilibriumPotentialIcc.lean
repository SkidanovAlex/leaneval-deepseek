import Submission.PotentialDefs
import Submission.EquilibriumMeasure
import Submission.EquilibriumPotential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric

/-!
# Equilibrium potential on the interval: contract A1′ (proof module)

Proves `SerreArithmetic.equilibrium_potential_on_Icc`: for `c < d` and
`x ∈ [c,d]`, the logarithmic potential of the equilibrium measure of `[c,d]`
at the real point `x` equals `logCap c d = −log((d−c)/4)`.

## Route

1. `equilibrium c d = Measure.map (chart c d) uniform01` (definition), so by
   `MeasureTheory.integral_map`:
   `logPotential (equilibrium c d) (x : ℂ)` =
   `∫ u, −log‖(x:ℂ) − (chart c d u : ℂ)‖ ∂uniform01`.
2. `chart c d u` is real, so by `Submission.PotentialDefs.log_norm_sub_ofReal`
   the integrand is `−log|x − chart c d u|`; then
   `Submission.Equilibrium.uniform01_integral` turns it into
   `∫ u in 0..1, −log|x − chart c d u|`.
3. `chart c d u = (c+d)/2 + (d−c)/2·cos(πu)`; substitute `t = π·u` with
   `intervalIntegral.integral_comp_mul_left (c := Real.pi)`:
   `∫₀¹ −log|x − (mid + half·cos(πu))|du = π⁻¹·∫₀^π −log|x − (mid+half·cos t)|dt`.
4. Negate `Submission.EquilibriumPotential.intervalIntegral_log_abs_chart_sub`
   (which gives `∫₀^π log|x − (mid + half·cos t)|dt = π·log((d−c)/4)`), so the
   result is `−log((d−c)/4) = logCap c d` (`PotentialDefs.logCap`, definition).
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.EquilibriumPotentialIcc

open Submission.PotentialDefs
open Submission.Equilibrium
open Submission.EquilibriumPotential

/-- `∫₀¹ log|x − chart c d u| du = log((d−c)/4)` for `x ∈ [c,d]`, `c < d`. -/
private lemma intervalIntegral_log_abs_chart_unit {c d x : ℝ} (hcd : c < d)
    (hx : x ∈ Set.Icc c d) :
    (∫ u in (0 : ℝ)..1, Real.log |x - chart c d u|) =
      Real.log ((d - c) / 4) := by
  let F : ℝ → ℝ := fun t => Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|
  have hF : (∫ t in (0 : ℝ)..Real.pi, F t) = Real.pi * Real.log ((d - c) / 4) := by
    simpa [F] using (intervalIntegral_log_abs_chart_sub (c := c) (d := d) (x := x) hcd hx)
  have hFpi : (fun u : ℝ => Real.log |x - chart c d u|) = fun u : ℝ => F (Real.pi * u) := by
    funext u
    rfl
  have hsub := intervalIntegral.integral_comp_mul_left (f := F) (c := Real.pi)
    (a := (0 : ℝ)) (b := (1 : ℝ)) (by positivity : (Real.pi : ℝ) ≠ 0)
  calc
    (∫ u in (0 : ℝ)..1, Real.log |x - chart c d u|)
        = (∫ u in (0 : ℝ)..1, F (Real.pi * u)) := by
          rw [hFpi]
    _ = (Real.pi)⁻¹ • (∫ t in Real.pi * (0 : ℝ)..Real.pi * (1 : ℝ), F t) := hsub
    _ = (Real.pi)⁻¹ * (∫ t in (0 : ℝ)..Real.pi, F t) := by
          simp [smul_eq_mul]
    _ = (Real.pi)⁻¹ * (Real.pi * Real.log ((d - c) / 4)) := by
          rw [hF]
    _ = Real.log ((d - c) / 4) := by
          rw [← mul_assoc, inv_mul_cancel₀ (Real.pi_ne_zero), one_mul]

/-- `U^{μ_eq}(x) = −log((d−c)/4)` for `x ∈ [c,d]`, `c < d`. -/
theorem equilibrium_potential_on_Icc {c d x : ℝ} (hcd : c < d)
    (hx : x ∈ Set.Icc c d) :
    logPotential (equilibrium c d) (x : ℂ) = logCap c d := by
  unfold logPotential logCap equilibrium
  have h1 : (∫ t : ℝ, -Real.log ‖(x : ℂ) - (t : ℂ)‖ ∂Measure.map (chart c d) uniform01) =
      (∫ u : ℝ, -Real.log ‖(x : ℂ) - (chart c d u : ℂ)‖ ∂uniform01) := by
    exact MeasureTheory.integral_map (φ := chart c d) (μ := uniform01)
      (f := fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖)
      (chart_measurable c d).aemeasurable
      (by
        have hmeas : Measurable fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖ := by
          fun_prop
        exact hmeas.aestronglyMeasurable)
  rw [h1]
  have hfun : (fun u : ℝ => -Real.log ‖(x : ℂ) - (chart c d u : ℂ)‖) =
      fun u : ℝ => -Real.log |x - chart c d u| := by
    funext u
    exact log_norm_sub_ofReal x (chart c d u)
  rw [hfun]
  rw [uniform01_integral]
  rw [intervalIntegral.integral_neg]
  rw [intervalIntegral_log_abs_chart_unit hcd hx]

end Submission.EquilibriumPotentialIcc
