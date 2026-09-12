import Submission.PotentialDefs
import Submission.Serre
import Submission.SerreExample
import Submission.SerreMean
import Submission.SupportConcentration
import Submission.ChartLogMoment
import Submission.NuChart
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Log-moment identity of Serre's measure (contract A4, equality part)

Proves `SerreArithmetic.serre_log_moment_eq`:

    ∫ x, log‖(x:ℂ)‖ ∂(serreMeasure gSerre aSerre bSerre)
        = −gSerre·log((a+2√(ab)+b)/(4ab)) + (1−gSerre)·log((a+2√(ab)+b)/4)

with `a = aSerre`, `b = bSerre`.

## Route

1. **Linearity** of the log-moment in the measure combination:
   `serreMeasure γ a b = ofReal γ • nu a b + ofReal (1−γ) • equilibrium a b`,
   so
       ∫ log‖(x:ℂ)‖ ∂(serreMeasure γ a b)
           = γ·∫ log‖x‖ dν + (1−γ)·∫ log‖x‖ dμ_eq
   (`integral_add_measure`/`integral_smul_measure`, `toReal_ofReal`;
   integrability of `x ↦ log‖(x:ℂ)‖` is fine: the measures are supported on
   `[a,b] ⊂ (0,∞)` (`SupportConcentration`), away from 0, and `log` is
   bounded there).

2. **Moment of the equilibrium measure**: with the chart
   `x(u) = (a+b)/2 + (b−a)/2·cos(πu) > 0` on `(0,1)`,
   `∫ log‖x‖ ∂μ_eq = ∫_u log(chart a b u) du = log((a+b+2√(ab))/4)` by
   `ChartLogMoment.log_moment_chart_eq` applied to `(a,b)`.
   (Here `log‖(x:ℂ)‖ = log x` since `x > 0`; chart values are in `[a,b] ⊂ (0,∞)`.)

3. **Moment of ν**: `ν` is the image of `μ_eq[c,d]`, `c = 1/b`, `d = 1/a`,
   under `t ↦ t⁻¹`, so
   `∫ log‖x‖ dν = ∫_u log‖(chart c d u)⁻¹‖ du = −∫_u log(chart c d u) du`
   = `−log((c+d+2√(cd))/4) = −log((a+2√(ab)+b)/(4ab))`
   by `ChartLogMoment.log_moment_chart_eq` applied to `(c,d)` (note
   `(c+d+2√(cd))/4 = (a+b+2√(ab))/(4ab)`).

4. Algebra: assemble with the definitions of `serreMeasure`, `gSerre`.

Use `NuChart.nu_integral_eq_chart` / `uniform01_integral` for the measure
changes; positivity of the chart (`chart_mem_Icc` with `c > 0`); `log` of
positive reals; `field_simp`/`ring_nf` at the end.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.SerreLogMoment

open Submission.PotentialDefs
open Submission.Serre
open Submission.SerreExample
open Submission.ChartLogMoment
open Submission.Equilibrium
open Submission.NuChart

/-- For `0 < x`, `log‖(x:ℂ)‖ = log x`. -/
lemma log_norm_ofReal_pos {x : ℝ} (hx : 0 < x) : Real.log ‖(x : ℂ)‖ = Real.log x := by
  rw [norm_complex_ofReal, abs_of_pos hx]

/-- `x ↦ log‖(x:ℂ)‖` is measurable. -/
lemma log_norm_measurable : Measurable (fun x : ℝ => Real.log ‖(x : ℂ)‖) := by
  fun_prop

/-- The log-norm is integrable against the equilibrium measure of `[a,b]`
(for `0 < a < b`: the measure lives on `[a,b] ⊂ (0,∞)` where it is bounded). -/
lemma equilibrium_integrable_log_norm {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ)‖) (equilibrium a b) := by
  have hb : 0 < b := lt_trans ha hab
  apply MeasureTheory.Integrable.of_mem_Icc (a := Real.log a) (b := Real.log b)
  · exact log_norm_measurable.aemeasurable
  · rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (equilibrium_compl_Icc a b hab.le)
    intro x hx hIcc
    -- hx : ¬ Real.log a ≤ Real.log ‖(x:ℂ)‖ ∧ ... ; hIcc : x ∈ Icc a b
    have hxpos : 0 < x := lt_of_lt_of_le ha hIcc.1
    apply hx
    rw [log_norm_ofReal_pos hxpos]
    constructor
    · exact Real.log_le_log ha hIcc.1
    · exact Real.log_le_log hxpos hIcc.2

/-- The log-norm is integrable against Serre's measure `ν`. -/
lemma nu_integrable_log_norm {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ)‖) (nu a b) := by
  have hb : 0 < b := lt_trans ha hab
  apply MeasureTheory.Integrable.of_mem_Icc (a := Real.log a) (b := Real.log b)
  · exact log_norm_measurable.aemeasurable
  · rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (Submission.SupportConcentration.nu_compl_Icc ha hab.le)
    intro x hx hIcc
    have hxpos : 0 < x := lt_of_lt_of_le ha hIcc.1
    apply hx
    rw [log_norm_ofReal_pos hxpos]
    constructor
    · exact Real.log_le_log ha hIcc.1
    · exact Real.log_le_log hxpos hIcc.2

/-- Log-moment of the equilibrium measure of `[a,b]`:
`∫ log‖x‖ dμ_eq = log((a + 2√(ab) + b)/4)`. -/
lemma equilibrium_log_moment {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂equilibrium a b) =
      Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
  have hmap : (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂equilibrium a b) =
      (∫ u : ℝ, Real.log ‖(chart a b u : ℂ)‖ ∂uniform01) := by
    unfold equilibrium
    exact MeasureTheory.integral_map (φ := chart a b) (μ := uniform01)
      (f := fun x : ℝ => Real.log ‖(x : ℂ)‖) (chart_measurable a b).aemeasurable
      (by exact log_norm_measurable.aestronglyMeasurable)
  have hfun : (fun u : ℝ => Real.log ‖(chart a b u : ℂ)‖) =
      fun u : ℝ => Real.log (chart a b u) := by
    funext u
    exact log_norm_ofReal_pos (lt_of_lt_of_le ha (chart_mem_Icc hab.le u).1)
  calc
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂equilibrium a b)
        = (∫ u : ℝ, Real.log ‖(chart a b u : ℂ)‖ ∂uniform01) := hmap
    _ = (∫ u : ℝ, Real.log (chart a b u) ∂uniform01) := by rw [hfun]
    _ = Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
      have hm := log_moment_chart_eq ha hab
      rw [hm]
      congr 1
      ring

/-- The reciprocal-chart log argument equals the direct one:
`(1/b + 1/a + 2·√(1/(ab)))/4 = (a + 2√(ab) + b)/(4ab)` for `0 < a < b`. -/
lemma nu_log_arg_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4 =
      (a + 2 * Real.sqrt (a * b) + b) / (4 * a * b) := by
  have hb : 0 < b := lt_trans ha hab
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hprod : b⁻¹ * a⁻¹ = (a * b)⁻¹ := by
    field_simp [ha.ne', hb.ne']
  have hsqrt : Real.sqrt (b⁻¹ * a⁻¹) = (Real.sqrt (a * b))⁻¹ := by
    rw [hprod]
    rw [Real.sqrt_inv]
  have hsne : Real.sqrt (a * b) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hab_pos)
  calc
    (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4
        = (b⁻¹ + a⁻¹ + 2 * (Real.sqrt (a * b))⁻¹) / 4 := by rw [hsqrt]
    _ = (a + 2 * Real.sqrt (a * b) + b) / (4 * a * b) := by
      field_simp [ha.ne', hb.ne', hsne]
      have hsqba : Real.sqrt (b * a) * Real.sqrt (b * a) = b * a := by
        rw [← sq]
        exact Real.sq_sqrt (mul_nonneg hb.le ha.le)
      nlinarith

/-- Log-moment of Serre's measure `ν`:
`∫ log‖x‖ dν = −log((a + 2√(ab) + b)/(4ab))`. -/
lemma nu_log_moment {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂nu a b) =
      -Real.log ((a + 2 * Real.sqrt (a * b) + b) / (4 * a * b)) := by
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < (b : ℝ)⁻¹ := inv_pos.mpr hb
  have hcd : (b : ℝ)⁻¹ < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  let f : ℝ → ℝ := fun x : ℝ => Real.log ‖(x : ℂ)‖
  have hmap : (∫ x : ℝ, f x ∂nu a b) =
      (∫ u : ℝ, f ((chart (b⁻¹) (a⁻¹) u)⁻¹) ∂uniform01) := by
    rw [nu_eq_map_inv_chart a b]
    exact MeasureTheory.integral_map (φ := fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹)
      (μ := uniform01) (f := f) (invChart_measurable a b).aemeasurable
      (by
        have hm : Measurable f := by dsimp [f]; fun_prop
        exact hm.aestronglyMeasurable)
  have hfun : (fun u : ℝ => f ((chart (b⁻¹) (a⁻¹) u)⁻¹)) =
      fun u : ℝ => -Real.log (chart (b⁻¹) (a⁻¹) u) := by
    funext u
    dsimp [f]
    have hu : chart (b⁻¹) (a⁻¹) u ∈ Set.Icc (b⁻¹) (a⁻¹) := chart_mem_Icc hcd.le u
    have hy : 0 < chart (b⁻¹) (a⁻¹) u := lt_of_lt_of_le hc hu.1
    rw [log_norm_ofReal_pos (inv_pos.mpr hy)]
    rw [Real.log_inv]
  calc
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂nu a b)
        = (∫ x : ℝ, f x ∂nu a b) := by
            simp [f]
    _ = (∫ u : ℝ, f ((chart (b⁻¹) (a⁻¹) u)⁻¹) ∂uniform01) := hmap
    _ = (∫ u : ℝ, -Real.log (chart (b⁻¹) (a⁻¹) u) ∂uniform01) := by rw [hfun]
    _ = -(∫ u : ℝ, Real.log (chart (b⁻¹) (a⁻¹) u) ∂uniform01) := by
            rw [MeasureTheory.integral_neg]
    _ = -Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) := by
            rw [log_moment_chart_eq hc hcd]
    _ = -Real.log ((a + 2 * Real.sqrt (a * b) + b) / (4 * a * b)) := by
      congr 2
      exact nu_log_arg_eq ha hab

/-- General log-moment identity: for `0 < a < b` and `0 ≤ γ ≤ 1`,
`∫ log‖(x:ℂ)‖ ∂(serreMeasure γ a b) = −γ·log((a+2√(ab)+b)/(4ab)) + (1−γ)·log((a+2√(ab)+b)/4)`. -/
lemma serre_log_moment_general {a b γ : ℝ} (ha : 0 < a) (hab : a < b)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂serreMeasure γ a b) =
      -γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / (4 * a * b)) +
        (1 - γ) * Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
  have hI1 : Integrable (fun x : ℝ => Real.log ‖(x : ℂ)‖) (ENNReal.ofReal γ • nu a b) :=
    (nu_integrable_log_norm ha hab).smul_measure ENNReal.ofReal_ne_top
  have hI2 : Integrable (fun x : ℝ => Real.log ‖(x : ℂ)‖)
      (ENNReal.ofReal (1 - γ) • equilibrium a b) :=
    (equilibrium_integrable_log_norm ha hab).smul_measure ENNReal.ofReal_ne_top
  unfold serreMeasure
  rw [MeasureTheory.integral_add_measure hI1 hI2]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal hγ0]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - γ)]
  rw [nu_log_moment ha hab]
  rw [equilibrium_log_moment ha hab]
  ring

/-- (A4) Log-moment identity of Serre's measure. -/
theorem serre_log_moment_eq :
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂serreMeasure gSerre aSerre bSerre) =
      -gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) /
          (4 * aSerre * bSerre)) +
        (1 - gSerre) * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4) := by
  exact serre_log_moment_general aSerre_pos a_lt_b (le_of_lt gSerre_pos) gSerre_le_one

end Submission.SerreLogMoment
