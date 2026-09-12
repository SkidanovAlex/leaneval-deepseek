import Submission.EquilibriumMeasure
import Submission.LogAffineCosIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Log-moment of the equilibrium measure of an interval

Sub-lemma of the balayage wiring (A2′) and of the Serre log-moment (A4):

    ∫ u, log(chart c d u) ∂uniform01 = log((c + d + 2·√(c·d))/4)      (0 < c < d)

(equivalently `∫ log|x| dμ_eq(x) = log((c+d+2√(cd))/4)`, the geometric-mean
type value of the arcsine law).  `chart c d u = (c+d)/2 + (d−c)/2·cos(πu)` is
positive on `(0,1)` when `c > 0`, so `log ∘ chart` is well-behaved.

## Route
1. `Submission.Equilibrium.uniform01_integral` turns the measure integral into
   `∫ u in 0..1, log(chart c d u)`.
2. Substitute `t = π·u` (`intervalIntegral.integral_comp_mul_left`, `c := π`,
   `Real.pi_ne_zero`): equals `π⁻¹·∫ t in 0..π, log((c+d)/2 + (d−c)/2·cos t)`.
3. Apply `Submission.LogAffineCosIntegral.integral_log_affine_cos` with
   `A = (c+d)/2`, `B = (d−c)/2` (need `0 < B < A`, which follows from
   `0 < c < d`).
4. Simplify `(A + √(A²−B²))/2 = (c + d + 2√(c·d))/4` (`A²−B² = c·d`) and the
   factor `π⁻¹·π`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.ChartLogMoment

open Submission.Equilibrium

/-- `∫ u, log(chart c d u) ∂uniform01 = log((c+d+2√(cd))/4)` for `0 < c < d`. -/
theorem log_moment_chart_eq {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    (∫ u : ℝ, Real.log (chart c d u) ∂uniform01) =
      Real.log ((c + d + 2 * Real.sqrt (c * d)) / 4) := by
  let A : ℝ := (c + d) / 2
  let B : ℝ := (d - c) / 2
  let G : ℝ → ℝ := fun t => Real.log (A + B * Real.cos t)
  have hB0 : 0 < B := by
    dsimp [B]
    exact div_pos (sub_pos.mpr hcd) (by norm_num : (0 : ℝ) < 2)
  have hBA : B < A := by
    dsimp [A, B]
    rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hGchart : ∀ u : ℝ, Real.log (chart c d u) = G (Real.pi * u) := by
    intro u
    dsimp [G, chart]
  have hcosint : (∫ t in (0 : ℝ)..Real.pi, G t) =
      Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) := by
    simpa [G] using
      (Submission.LogAffineCosIntegral.integral_log_affine_cos (A := A) (B := B) hB0 hBA)
  have hsq : A ^ 2 - B ^ 2 = c * d := by
    dsimp [A, B]
    ring
  have hsqrt : Real.sqrt (A ^ 2 - B ^ 2) = Real.sqrt (c * d) := by
    rw [hsq]
  have hsimpl : (A + Real.sqrt (A ^ 2 - B ^ 2)) / 2 = (c + d + 2 * Real.sqrt (c * d)) / 4 := by
    rw [hsqrt]
    dsimp [A, B]
    ring
  calc
    (∫ u : ℝ, Real.log (chart c d u) ∂uniform01)
        = (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [uniform01_integral]
    _ = (∫ u in (0 : ℝ)..1, G (Real.pi * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            exact hGchart u
    _ = (Real.pi : ℝ)⁻¹ * (∫ t in (0 : ℝ)..Real.pi, G t) := by
            rw [intervalIntegral.integral_comp_mul_left (f := G) (c := Real.pi)
              (a := (0 : ℝ)) (b := 1) Real.pi_ne_zero]
            simp [smul_eq_mul]
    _ = (Real.pi : ℝ)⁻¹ * (Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2)) := by
            rw [hcosint]
    _ = Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
    _ = Real.log ((c + d + 2 * Real.sqrt (c * d)) / 4) := by
            rw [hsimpl]

end Submission.ChartLogMoment
