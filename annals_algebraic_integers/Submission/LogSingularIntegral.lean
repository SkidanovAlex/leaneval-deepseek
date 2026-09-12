import Submission.EquilibriumMeasure
import Submission.Serre
import Submission.SerreExample
import Submission.NuChart
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Complex.Basic

/-!
# Logarithmic singularity is integrable against the equilibrium & ν measures (C1b)

For the finite-sum log identity (C1) one needs each `x ↦ log‖(x:ℂ) − r‖`
(`r` real inside the interval) to be integrable against the two ingredients of
Serre's measure.  The only difficulty is the logarithmic singularity at the
point `r` itself; it is integrable because the measures are pushforwards of
Lebesgue on `(0,1)` along the chart `u ↦ (c+d)/2 + (d−c)/2·cos(πu)`, and the
logarithm of any real-analytic function is interval integrable
(`MeromorphicOn.intervalIntegrable_log`, in
`Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic`).

## Route for `equilibrium_log_sub_integrable`

`equilibrium a b` is the image of `uniform01` under `u ↦ chart a b u`.  Since
`Real.log` satisfies `log x = log|x|` (it is even: `Real.log_abs`), the
integrand pulled back to the parameter is `log ∘ (u ↦ chart a b u − r)` with
`chart a b u − r` a real-analytic (hence real-meromorphic, `AnalyticOnNhd.meromorphicOn`)
function on `[[0,1]]`; `MeromorphicOn.intervalIntegrable_log` then gives the
interval integrability.  (The hypotheses `a < b`, `r ∈ [a,b]` are not even
needed: the same argument works for any real `a,b,r`.)

## Route for `nu_log_sub_integrable` (0 < a < b, r ∈ [a,b])

`ν = ν_{[a,b]}` is the image of `uniform01` under
`u ↦ (chart (b⁻¹) (a⁻¹) u)⁻¹` (`Submission.NuChart.nu_eq_map_inv_chart`).
For `0 < a < b` the reciprocal chart stays in `[1/b, 1/a] ⊂ (0,∞)`, so
`u ↦ (chart (b⁻¹) (a⁻¹) u)⁻¹ − r` is real analytic (inversion is analytic
away from zero) and the same interval-log-integrability argument applies.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.LogSingularIntegral

open Submission.Equilibrium
open Submission.Serre
open Submission.NuChart

/-- For real `y`, `‖(y:ℂ) − (r:ℂ)‖ = |y−r|` and `Real.log` is even
(`log x = log|x|`), so the complex-norm logarithm is the real logarithm of
`y − r`. -/
lemma real_log_norm_sub (y r : ℝ) :
    Real.log ‖(y : ℂ) - (r : ℂ)‖ = Real.log (y - r) := by
  have h1 : ‖(y : ℂ) - (r : ℂ)‖ = |y - r| := by
    have hcast : (y : ℂ) - (r : ℂ) = ((y - r : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hcast]
    simpa using (Complex.norm_real (y - r))
  rw [h1]
  exact Real.log_abs (y - r)

/-- Integrability against `uniform01` (= Lebesgue restricted to `(0,1]`)
is interval integrability over `[0,1]`. -/
lemma intervalIntegrable_uniform01 {f : ℝ → ℝ} :
    Integrable f uniform01 ↔ IntervalIntegrable f volume (0 : ℝ) 1 := by
  constructor
  · intro hf
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) (f := f)
      (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)).mpr hf
  · intro hII
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) (f := f)
      (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)).mp hII

/-- `x ↦ log‖(x:ℂ) − (r:ℂ)‖` is Borel measurable (hence AE strongly measurable
against any measure on `ℝ`). -/
lemma measurable_log_norm_sub (r : ℝ) :
    Measurable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) := by
  fun_prop

/-- `log‖(x:ℂ) − (r:ℂ)‖` is integrable against the equilibrium measure of
`[a,b]` when `a < b` and `r ∈ [a,b]` (logarithmic singularity included). -/
lemma equilibrium_log_sub_integrable {a b r : ℝ} (hab : a < b) (hr : r ∈ Set.Icc a b) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) (equilibrium a b) := by
  let G : ℝ → ℝ := fun x => Real.log ‖(x : ℂ) - (r : ℂ)‖
  let f : ℝ → ℝ := fun u => chart a b u - r
  have hAnal : AnalyticOnNhd ℝ f Set.univ := by
    intro x hx
    unfold f chart
    fun_prop
  have hII : IntervalIntegrable (Real.log ∘ f) volume (0 : ℝ) 1 := by
    apply MeromorphicOn.intervalIntegrable_log
    exact ((AnalyticOnNhd.meromorphicOn (f := f) hAnal
      : MeromorphicOn f Set.univ).mono_set (by intro x hx; trivial))
  have hEqOn : Set.EqOn (Real.log ∘ f)
      (fun u : ℝ => Real.log ‖(chart a b u : ℂ) - (r : ℂ)‖) (Set.uIoc (0 : ℝ) 1) := by
    intro u hu
    simp [f, (real_log_norm_sub (chart a b u) r).symm]
  have hII' : IntervalIntegrable (fun u : ℝ => Real.log ‖(chart a b u : ℂ) - (r : ℂ)‖)
      volume (0 : ℝ) 1 := by
    exact ((intervalIntegrable_congr (μ := volume) (a := (0 : ℝ)) (b := 1) hEqOn).mp hII)
  have hUnif : Integrable (fun u : ℝ => Real.log ‖(chart a b u : ℂ) - (r : ℂ)‖) uniform01 := by
    exact (intervalIntegrable_uniform01).mpr hII'
  have hGmeas : Measurable G := by
    dsimp [G]
    fun_prop
  have hGae : AEStronglyMeasurable G (Measure.map (chart a b) uniform01) := by
    exact AEMeasurable.aestronglyMeasurable hGmeas.aemeasurable
  have hchartAe : AEMeasurable (chart a b) uniform01 := (chart_measurable a b).aemeasurable
  have hpull : Integrable G (Measure.map (chart a b) uniform01) := by
    apply (integrable_map_measure hGae hchartAe).mpr
    change Integrable (fun u : ℝ => Real.log ‖(chart a b u : ℂ) - (r : ℂ)‖) uniform01
    simpa [G] using hUnif
  simpa [equilibrium, G] using hpull

/-- `log‖(x:ℂ) − (r:ℂ)‖` is integrable against Serre's `ν` measure on `[a,b]`
when `0 < a < b` and `r ∈ [a,b]`. -/
lemma nu_log_sub_integrable {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Set.Icc a b) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) (nu a b) := by
  rw [nu_eq_map_inv_chart a b]
  let G : ℝ → ℝ := fun x => Real.log ‖(x : ℂ) - (r : ℂ)‖
  let φ : ℝ → ℝ := fun u => (chart (b⁻¹) (a⁻¹) u)⁻¹
  let H : ℝ → ℝ := fun u => Real.log ‖(φ u : ℂ) - (r : ℂ)‖
  have hb : 0 < b := lt_trans ha hab
  have hcd : (b⁻¹ : ℝ) ≤ a⁻¹ := by
    exact le_of_lt ((inv_lt_inv₀ (a := b) (b := a) hb ha).2 hab)
  have hc : 0 < (b⁻¹ : ℝ) := inv_pos.mpr hb
  have hChartPos : ∀ u : ℝ, 0 < chart (b⁻¹) (a⁻¹) u := by
    intro u
    exact lt_of_lt_of_le hc ((chart_mem_Icc hcd u).1)
  -- u ↦ φ u − r is real analytic on [[0,1]] (inversion is analytic away from 0)
  have hgMer : MeromorphicOn (fun u : ℝ => φ u - r) (Set.uIcc (0 : ℝ) 1) := by
    apply AnalyticOnNhd.meromorphicOn
    intro x hx
    have hchart : AnalyticAt ℝ (fun u : ℝ => chart (b⁻¹) (a⁻¹) u) x := by
      unfold chart
      fun_prop
    have hinv : AnalyticAt ℝ (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) x := by
      exact AnalyticAt.inv hchart (ne_of_gt (hChartPos x))
    have : AnalyticAt ℝ (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹ - r) x := hinv.sub analyticAt_const
    simpa [φ] using this
  have hII : IntervalIntegrable (Real.log ∘ (fun u : ℝ => φ u - r)) volume (0 : ℝ) 1 := by
    apply MeromorphicOn.intervalIntegrable_log
    simpa [φ] using hgMer
  have hEqOn : Set.EqOn (Real.log ∘ (fun u : ℝ => φ u - r)) H (Set.uIoc (0 : ℝ) 1) := by
    intro u hu
    simp [H, φ, (real_log_norm_sub (φ u) r).symm]
  have hII' : IntervalIntegrable H volume (0 : ℝ) 1 := by
    exact ((intervalIntegrable_congr (μ := volume) (a := (0 : ℝ)) (b := 1) hEqOn).mp hII)
  have hUnif : Integrable H uniform01 := by
    exact (intervalIntegrable_uniform01).mpr hII'
  have hGmeas : Measurable G := by dsimp [G]; fun_prop
  have hGae : AEStronglyMeasurable G (Measure.map φ uniform01) := by
    exact AEMeasurable.aestronglyMeasurable hGmeas.aemeasurable
  have hφae : AEMeasurable φ uniform01 := (invChart_measurable a b).aemeasurable
  have hpull : Integrable G (Measure.map φ uniform01) := by
    apply (integrable_map_measure hGae hφae).mpr
    change Integrable (fun u : ℝ => Real.log ‖(φ u : ℂ) - (r : ℂ)‖) uniform01
    simpa [H] using hUnif
  simpa [G, φ] using hpull

end Submission.LogSingularIntegral
