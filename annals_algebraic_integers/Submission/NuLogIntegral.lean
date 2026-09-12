import Submission.EquilibriumMeasure
import Submission.Serre
import Submission.NuChart
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

/-!
# The logarithmic singularity against Serre's `ν` measure (C1b/ν)

`x ↦ log‖(x:ℂ) − r‖` is integrable against `ν = ν_{[a,b]}` for `0 < a < b`
and `r ∈ [a,b]`.

Route: `ν = map (fun u ↦ (chart (1/b) (1/a) u)⁻¹) uniform01`
(`NuChart.nu_eq_map_inv_chart`), so by `MeasureTheory.integrable_map_measure`
it suffices to show the pulled-back integrand

    u ↦ log‖((chart (1/b) (1/a) u)⁻¹ : ℂ) − (r : ℂ)‖
      = log|(chart (1/b) (1/a) u)⁻¹ − r|

interval-integrable over `[0,1]`. Since `chart c d u ≥ c > 0` on `[0,1]`
(`chart_mem_Icc`), the function `u ↦ (chart c d u)⁻¹ − r` is real-analytic on a
neighbourhood of `[0,1]`, hence real-meromorphic, and
`MeromorphicOn.intervalIntegrable_log_norm`
(`Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic`) makes its
log-norm interval-integrable — the logarithmic singularity is integrable.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.NuLogIntegral

open Submission.Equilibrium
open Submission.Serre
open Submission.NuChart

/-- The chart `u ↦ chart c d u` is real-analytic at every point. -/
lemma analyticAt_chart (c d u₀ : ℝ) : AnalyticAt ℝ (chart c d) u₀ := by
  change AnalyticAt ℝ (fun u : ℝ => (c + d) / 2 + (d - c) / 2 * Real.cos (Real.pi * u)) u₀
  fun_prop

/-- `u ↦ (chart c d u)⁻¹ − r` is real-analytic at `u₀` when the chart does not
vanish there. -/
lemma analyticAt_invChart_sub {c d r u₀ : ℝ} (h : chart c d u₀ ≠ 0) :
    AnalyticAt ℝ (fun u : ℝ => (chart c d u)⁻¹ - r) u₀ := by
  have hchart : AnalyticAt ℝ (chart c d) u₀ := analyticAt_chart c d u₀
  have hinvReal : AnalyticAt ℝ (fun t : ℝ => t⁻¹) (chart c d u₀) := by
    simpa using (analyticAt_inv (𝕜 := ℝ) (𝕝 := ℝ) h)
  have hcomp1 : AnalyticAt ℝ (fun u : ℝ => (chart c d u)⁻¹) u₀ := hinvReal.comp hchart
  exact hcomp1.sub (analyticAt_const (𝕜 := ℝ) (x := u₀) (v := r))

/-- The chart stays positive when the lower endpoint is positive. -/
lemma chart_pos_of_pos {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (u : ℝ) : 0 < chart c d u := by
  have hmem : chart c d u ∈ Set.Icc c d := chart_mem_Icc hcd u
  exact lt_of_lt_of_le hc hmem.1

/-- `u ↦ (chart c d u)⁻¹ − r` is real-meromorphic on `[0,1]` for `0 < c ≤ d`. -/
lemma meromorphicOn_invChart_sub {c d r : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    MeromorphicOn (fun u : ℝ => (chart c d u)⁻¹ - r) (Set.uIcc (0 : ℝ) 1) := by
  intro u₀ _
  apply AnalyticAt.meromorphicAt
  exact analyticAt_invChart_sub (ne_of_gt (chart_pos_of_pos hc hcd u₀))

/-- `u ↦ log|(chart c d u)⁻¹ − r|` is interval-integrable over `[0,1]` for
`0 < c ≤ d`. -/
lemma intervalIntegrable_log_invChart_sub {c d r : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    IntervalIntegrable (fun u : ℝ => Real.log |(chart c d u)⁻¹ - r|) volume 0 1 := by
  have hmero : MeromorphicOn (fun u : ℝ => (chart c d u)⁻¹ - r) (Set.uIcc (0 : ℝ) 1) :=
    meromorphicOn_invChart_sub hc hcd
  have h := MeromorphicOn.intervalIntegrable_log_norm
    (f := fun u : ℝ => (chart c d u)⁻¹ - r) hmero
  simpa using h

/-- Interval-integrability over `[0,1]` gives integrability against `uniform01`. -/
lemma integrable_uniform01_of_interval {f : ℝ → ℝ} (h : IntervalIntegrable f volume 0 1) :
    Integrable f uniform01 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (a := 0) (b := 1)
    (by norm_num : (0 : ℝ) ≤ 1)] at h
  simp [MeasureTheory.IntegrableOn] at h
  exact h

/-- For real `x`, `log‖(x:ℂ) − (r:ℂ)‖ = log|x − r|`. -/
lemma log_norm_sub_complex (x r : ℝ) : Real.log ‖(x : ℂ) - (r : ℂ)‖ = Real.log |x - r| := by
  rw [← Complex.ofReal_sub]
  exact congrArg Real.log (RCLike.norm_ofReal (x - r))

/-- `x ↦ log‖(x:ℂ) − (r:ℂ)‖` is Borel measurable. -/
lemma log_sub_measurable (r : ℝ) : Measurable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) := by
  apply ContinuousOn.measurable_of_countable_compl (s := ({r}ᶜ : Set ℝ))
  · intro x hx
    have hxr : x ≠ r := by simpa using hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log
    · fun_prop
    · exact norm_ne_zero_iff.mpr (by
        intro h
        apply hxr
        exact Complex.ofReal_inj.mp (sub_eq_zero.mp h))
  · simp

/-- `log‖(x:ℂ) − (r:ℂ)‖` is integrable against Serre's `ν` measure on `[a,b]`
when `0 < a < b` and `r ∈ [a,b]`. -/
lemma nu_log_sub_integrable {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Set.Icc a b) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) (nu a b) := by
  have hmem : r ∈ Set.Icc a b := hr
  have hb : 0 < b := lt_trans ha hab
  have hab' : a ≤ b := le_of_lt hab
  have hcpos : 0 < (b⁻¹ : ℝ) := inv_pos.mpr hb
  have hcd : (b⁻¹ : ℝ) ≤ (a⁻¹ : ℝ) := (inv_le_inv₀ hb ha).mpr hab'
  let φ : ℝ → ℝ := fun u => (chart (b⁻¹) (a⁻¹) u)⁻¹
  let F : ℝ → ℝ := fun x => Real.log ‖(x : ℂ) - (r : ℂ)‖
  have hφmeas : Measurable φ := by
    dsimp [φ]
    exact measurable_inv.comp (chart_measurable (b⁻¹) (a⁻¹))
  have hFmeas : Measurable F := by
    dsimp [F]
    exact log_sub_measurable r
  have hii : IntervalIntegrable (fun u : ℝ => Real.log |φ u - r|) volume 0 1 := by
    dsimp [φ]
    exact intervalIntegrable_log_invChart_sub (c := (b⁻¹ : ℝ)) (d := (a⁻¹ : ℝ)) (r := r) hcpos hcd
  have hEqOn : Set.EqOn (F ∘ φ) (fun u : ℝ => Real.log |φ u - r|) (Set.uIoc (0 : ℝ) 1) := by
    intro u _
    dsimp [F]
    exact log_norm_sub_complex (φ u) r
  have hS_ii : IntervalIntegrable (F ∘ φ) volume 0 1 := by
    exact (intervalIntegrable_congr (a := 0) (b := 1) (μ := volume) hEqOn).mpr hii
  have hU : Integrable (F ∘ φ) uniform01 := integrable_uniform01_of_interval hS_ii
  have htr : Integrable F (Measure.map φ uniform01) := by
    exact (integrable_map_measure (g := F) (f := φ) (μ := uniform01)
      hFmeas.aestronglyMeasurable hφmeas.aemeasurable).mpr hU
  rw [nu_eq_map_inv_chart a b]
  exact htr

end Submission.NuLogIntegral
