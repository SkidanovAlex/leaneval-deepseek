import Submission.NuChart
import Submission.ChartLogMoment
import Submission.EquilibriumPotentialIcc
import Submission.PotentialDefs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Balayage identity on the interval: contract A2′ (proof module)

Proves `SerreArithmetic.balay_potential_on_Icc`: for `0 < a < b` and
`x ∈ [a,b]`,

    logPotential (nu a b) (x : ℂ) + Real.log ‖(x : ℂ)‖
        = Real.log ((a + 2·√(a·b) + b) / (b − a)).

## Mathematical content (all ingredients already verified)

ν = image of the equilibrium measure of `[c,d] = [1/b, 1/a]` under inversion,
and the equilibrium measure is the image of `uniform01` under the chart; so by
`NuChart.nu_integral_eq_chart`,

    logPotential (nu a b) (x : ℂ)
        = ∫ u, −log‖(x:ℂ) − ((chart c d u : ℂ)⁻¹)‖ ∂uniform01 .

For u with `t := chart c d u > 0` (true on (0,1) since c > 0), the real-log
algebra `|x − t⁻¹| = |1 − x·t| / t` gives

    −log|x − t⁻¹| = −log|1 − x·t| + log t ,

hence (split the integral over `u`):

    logPotential (nu a b) (x:ℂ) = A + B

with `A = ∫ u, −log|1 − x·(chart c d u)| ∂uniform01` and
`B = ∫ u, log (chart c d u) ∂uniform01`.

* `B` is the log-moment of the chart: by `ChartLogMoment.log_moment_chart_eq`,
  `B = log((c + d + 2·√(c·d))/4)`.

* For `A`: since `x ∈ [a,b]`, `w := x⁻¹ ∈ [c,d]` (inverse is antitone on
  positives), and `|1 − x·t| = x·|x⁻¹ − t|` (`x > 0`), so
  `A = −∫ u, log‖(w:ℂ) − (chart c d u : ℂ)‖ ∂uniform01 − log x`
  (log x comes out with mass 1), i.e.
  `A = logPotential (equilibrium c d) (w:ℂ) − log x`
  and by `EquilibriumPotentialIcc.equilibrium_potential_on_Icc` (with `w ∈ [c,d]`),
  `A = logCap c d − log x = −log((d−c)/4) − log x`.

Summing: `logPotential (nu a b)(x:ℂ) + log x = −log((d−c)/4) + log((c+d+2√(cd))/4)`,
which equals `log((c+d+2√(cd))/(d−c))`.  With `c = 1/b`, `d = 1/a` the algebra
`(c+d+2√(cd))/(d−c) = (a + 2√(ab) + b)/(b−a)` finishes the claim
(and `Real.log ‖(x:ℂ)‖ = log x` since `x > 0`).

## Notes for the machine-checked proof
* After `NuChart.nu_integral_eq_chart`, use `uniform01_integral` to move to
  interval integrals in `u ∈ 0..1`; use `chart_measurable`, positivity of the
  chart (`chart_mem_Icc`, `c > 0`), `Real.log_mul` / `Real.log_div` /
  `Real.log_inv`, and `abs` identities with the positivity of `x` and `t`.
* The log-singular integrands (`log|1 − x·(chart u)|`, which has a
  log-singularity where `x·chart u = 1`) are `IntervalIntegrable` /
  `Integrable`: singularities of `log∘|affine|` are integrable in one
  dimension (substitute `v = u − u₀` and use
  `integral_log_from_zero`-style facts or mathlib's
  `intervalIntegrable_log`); alternatively split off neighborhoods.
* `AEStronglyMeasurable` hypotheses of the change-of-variables lemmas are
  discharged by `Continuous.aestronglyMeasurable`/`Measurable.stronglyMeasurable`
  (the integrands are continuous off a null set / measurable).
* Algebra at the end: `field_simp`/`ring_nf` with `a,b ≠ 0`, `Real.sq_sqrt`,
  `Real.sqrt_mul`.
-/

noncomputable section

open MeasureTheory
open scoped Real Interval

namespace Submission.BalayOnIcc

open Submission.NuChart
open Submission.ChartLogMoment
open Submission.PotentialDefs
open Submission.Equilibrium
open Submission.Serre

/-! ## Small helpers -/

/-- The chart `u ↦ chart c d u` is strictly decreasing on `[0,1]` when `c < d`. -/
private lemma chart_strictAntiOn {c d : ℝ} (hcd : c < d) :
    StrictAntiOn (chart c d) (Set.Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hπu0 : 0 ≤ Real.pi * u := mul_nonneg (le_of_lt Real.pi_pos) hu.1
  have hπv1 : Real.pi * v ≤ Real.pi := by
    simpa using mul_le_mul_of_nonneg_left hv.2 (le_of_lt Real.pi_pos)
  have hcospi : Real.cos (Real.pi * v) < Real.cos (Real.pi * u) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hπu0 hπv1 (mul_lt_mul_of_pos_left huv Real.pi_pos)
  have hB : 0 < (d - c) / 2 := by positivity
  unfold chart
  have hprod : (d - c) / 2 * (Real.cos (Real.pi * v) - Real.cos (Real.pi * u)) < 0 :=
    mul_neg_of_pos_of_neg hB (sub_neg.mpr hcospi)
  linarith

/-- The set of parameters `u ∈ (0,1]` where the chart hits a fixed value has
volume zero (the chart is injective on `[0,1]`). -/
private lemma preimage_chart_meas_zero {c d w : ℝ} (hcd : c < d) :
    (volume : Measure ℝ) {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ chart c d u = w} = 0 := by
  let S : Set ℝ := {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ chart c d u = w}
  have hsubsing : S.Subsingleton := by
    intro u hu v hv
    have hInj := (chart_strictAntiOn hcd).injOn
    have hucc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hu.1.1, hu.1.2⟩
    have hvcc : v ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hv.1.1, hv.1.2⟩
    exact hInj hucc hvcc (by rw [hu.2, hv.2])
  exact hsubsing.measure_zero (volume : Measure ℝ)

/-- Real-log identity: `−log|x − t⁻¹| = −log x − log|x⁻¹ − t| + log t`
for `x, t > 0`, `t ≠ x⁻¹`. -/
private lemma log_inv_abs (x t : ℝ) (hx : 0 < x) (ht : 0 < t) (htne : t ≠ x⁻¹) :
    -Real.log |x - t⁻¹| = -Real.log x - Real.log |x⁻¹ - t| + Real.log t := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hne : 1 - x * t ≠ 0 := by
    intro h
    have hxt : x * t = 1 := by linarith
    have : x⁻¹ = t := by
      rw [mul_comm] at hxt
      exact inv_eq_of_mul_eq_one_left hxt
    exact htne this.symm
  have hneabs : |1 - x * t| ≠ 0 := abs_ne_zero.mpr hne
  have hwne : x⁻¹ - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htne)
  have hwabs : |x⁻¹ - t| ≠ 0 := abs_ne_zero.mpr hwne
  have hEq : |x - t⁻¹| = |1 - x * t| * t⁻¹ := by
    have hxmt : x - t⁻¹ = (x * t - 1) * t⁻¹ := by
      field_simp [ht0]
    calc
      |x - t⁻¹| = |(x * t - 1) * t⁻¹| := by rw [hxmt]
      _ = |x * t - 1| * |t⁻¹| := abs_mul (x * t - 1) t⁻¹
      _ = |x * t - 1| * t⁻¹ := by rw [abs_of_pos (inv_pos.mpr ht)]
      _ = |1 - x * t| * t⁻¹ := by rw [abs_sub_comm]
  have hA : Real.log x + Real.log |x⁻¹ - t| = Real.log |1 - x * t| := by
    rw [← Real.log_mul hx0 hwabs]
    congr 1
    calc
      x * |x⁻¹ - t| = |x| * |x⁻¹ - t| := by rw [abs_of_pos hx]
      _ = |x * (x⁻¹ - t)| := (abs_mul x (x⁻¹ - t)).symm
      _ = |1 - x * t| := by
            congr 2
            calc
              x * (x⁻¹ - t) = x * x⁻¹ - x * t := by ring
              _ = 1 - x * t := by rw [mul_inv_cancel₀ hx0]
  have hB : Real.log t + Real.log |x - t⁻¹| = Real.log |1 - x * t| := by
    have hlog : Real.log |x - t⁻¹| = Real.log |1 - x * t| - Real.log t := by
      rw [hEq]
      rw [Real.log_mul hneabs (inv_ne_zero ht0)]
      rw [Real.log_inv]
      ring
    linarith
  have hAB : Real.log x + Real.log |x⁻¹ - t| = Real.log t + Real.log |x - t⁻¹| := by
    rw [hA, hB]
  linarith

/-- Interval integrability on `[0,1]` of `u ↦ log(chart c d u)` when the
chart stays positive. -/
private lemma log_chart_integrable {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    IntervalIntegrable (fun u : ℝ => Real.log (chart c d u)) volume (0 : ℝ) 1 := by
  have hpos : ∀ u : ℝ, 0 < chart c d u := by
    intro u
    have hmem := chart_mem_Icc hcd u
    exact lt_of_lt_of_le hc hmem.1
  have hcont : Continuous fun u : ℝ => Real.log (chart c d u) := by
    apply Continuous.log (chart_continuous c d)
    intro u
    exact ne_of_gt (hpos u)
  exact hcont.intervalIntegrable _ _

/-- Interval integrability on `[0,1]` of `u ↦ log|w − chart c d u|`
(log-singular where the chart meets `w`, integrable in dimension one). -/
private lemma log_abs_chart_integrable (c d w : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log |w - chart c d u|) volume (0 : ℝ) 1 := by
  have hf : MeromorphicOn (fun u : ℝ => w - chart c d u) [[(0 : ℝ), 1]] := by
    unfold chart
    apply AnalyticOnNhd.meromorphicOn
    intro x hx
    fun_prop
  have hl := hf.intervalIntegrable_log
  convert hl using 1
  · funext u
    rw [Real.log_abs]
    rfl

/-- The balayage integrand equals its algebraic split almost everywhere on
`(0,1]`: `−log|x − (chart u)⁻¹| = (−log x) + (−log|x⁻¹ − chart u|) + log(chart u)`. -/
private lemma ae_balay_split {c d x : ℝ} (hc : 0 < c) (hcd : c < d) (hx0 : 0 < x) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (0 : ℝ) 1 →
      (-Real.log |x - (chart c d u)⁻¹|) =
        ((-Real.log x) + (-Real.log |x⁻¹ - chart c d u|)) + Real.log (chart c d u) := by
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null
  · intro u hu
    dsimp at hu
    push Not at hu
    rcases hu with ⟨huI, hne⟩
    have hchart : chart c d u = x⁻¹ := by
      by_contra hch
      have ht : 0 < chart c d u := by
        have hmem := chart_mem_Icc (le_of_lt hcd) u
        exact lt_of_lt_of_le hc hmem.1
      have hEq := log_inv_abs x (chart c d u) hx0 ht hch
      have hsplit : -Real.log |x - (chart c d u)⁻¹| =
          ((-Real.log x) + (-Real.log |x⁻¹ - chart c d u|)) + Real.log (chart c d u) := by
        linarith
      exact hne hsplit
    show u ∈ Set.Ioc (0 : ℝ) 1 ∧ chart c d u = x⁻¹
    exact ⟨by simpa using huI, hchart⟩
  · exact preimage_chart_meas_zero (c := c) (d := d) (w := x⁻¹) hcd

/-- Splitting the balayage integral over `u ∈ [0,1]`:
`∫₀¹ −log|x − (chart u)⁻¹| = −log x + ∫₀¹ −log|x⁻¹ − chart u| + ∫₀¹ log(chart u)`. -/
private lemma split_balay_integral {c d x : ℝ} (hc : 0 < c) (hcd : c < d) (hx0 : 0 < x) :
    (∫ u in (0 : ℝ)..1, -Real.log |x - (chart c d u)⁻¹|)
      = -Real.log x
          + (∫ u in (0 : ℝ)..1, -Real.log |x⁻¹ - chart c d u|)
          + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
  let p1 : ℝ → ℝ := fun _ : ℝ => -Real.log x
  let p2 : ℝ → ℝ := fun u => -Real.log |x⁻¹ - chart c d u|
  let p3 : ℝ → ℝ := fun u => Real.log (chart c d u)
  have ip3 : IntervalIntegrable p3 volume (0 : ℝ) 1 := by
    dsimp [p3]
    exact log_chart_integrable hc (le_of_lt hcd)
  have ip2 : IntervalIntegrable p2 volume (0 : ℝ) 1 := by
    dsimp [p2]
    exact (log_abs_chart_integrable c d x⁻¹).neg
  have ip1 : IntervalIntegrable p1 volume (0 : ℝ) 1 := intervalIntegrable_const
  calc
    (∫ u in (0 : ℝ)..1, -Real.log |x - (chart c d u)⁻¹|)
        = (∫ u in (0 : ℝ)..1,
            ((-Real.log x) + (-Real.log |x⁻¹ - chart c d u|)) + Real.log (chart c d u)) := by
            exact intervalIntegral.integral_congr_ae (ae_balay_split hc hcd hx0)
    _ = (∫ u in (0 : ℝ)..1, p1 u + p2 u)
        + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [intervalIntegral.integral_add (IntervalIntegrable.add ip1 ip2) ip3]
    _ = (∫ u in (0 : ℝ)..1, p1 u)
        + (∫ u in (0 : ℝ)..1, -Real.log |x⁻¹ - chart c d u|)
        + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [intervalIntegral.integral_add ip1 ip2]
    _ = -Real.log x
        + (∫ u in (0 : ℝ)..1, -Real.log |x⁻¹ - chart c d u|)
        + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [intervalIntegral.integral_const]
            simp

/-- The equilibrium-potential term in u-space:
`∫₀¹ −log|w − chart c d u| du = logCap c d` for `w ∈ [c,d]`, `c < d`.
(A1′ transported from the measure-level statement.) -/
private lemma interval_neg_log_abs_chart_sub {c d w : ℝ} (hcd : c < d)
    (hw : w ∈ Set.Icc c d) :
    (∫ u in (0 : ℝ)..1, -Real.log |w - chart c d u|) = logCap c d := by
  have hA1 := EquilibriumPotentialIcc.equilibrium_potential_on_Icc hcd hw
  unfold logPotential at hA1
  unfold equilibrium at hA1
  have hmap : (∫ t : ℝ, -Real.log ‖(w : ℂ) - (t : ℂ)‖
        ∂Measure.map (chart c d) uniform01) =
      (∫ u : ℝ, -Real.log ‖(w : ℂ) - (chart c d u : ℂ)‖ ∂uniform01) := by
    exact MeasureTheory.integral_map (φ := chart c d) (μ := uniform01)
      (f := fun t : ℝ => -Real.log ‖(w : ℂ) - (t : ℂ)‖) (chart_measurable c d).aemeasurable
      (by
        have hmeas : Measurable fun t : ℝ => -Real.log ‖(w : ℂ) - (t : ℂ)‖ := by fun_prop
        exact hmeas.aestronglyMeasurable)
  rw [hmap] at hA1
  have hfun : (fun u : ℝ => -Real.log ‖(w : ℂ) - (chart c d u : ℂ)‖) =
      fun u : ℝ => -Real.log |w - chart c d u| := by
    funext u
    exact log_norm_sub_ofReal w (chart c d u)
  rw [hfun] at hA1
  rw [uniform01_integral] at hA1
  exact hA1

/-- The log-moment term in u-space:
`∫₀¹ log(chart c d u) du = log((c + d + 2√(cd))/4)` for `0 < c < d`. -/
private lemma interval_log_chart {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) =
      Real.log ((c + d + 2 * Real.sqrt (c * d)) / 4) := by
  have h := log_moment_chart_eq hc hcd
  rw [uniform01_integral] at h
  exact h

/-- The balayage integral identity in chart coordinates:
`∫₀¹ −log|x − (chart c d u)⁻¹| du = −log x + logCap c d + log((c+d+2√(cd))/4)`
for `0 < c < d`, `x > 0`, `x⁻¹ ∈ [c,d]`. -/
private lemma balay_integral_eq {c d x : ℝ} (hc : 0 < c) (hcd : c < d)
    (hx0 : 0 < x) (hw : x⁻¹ ∈ Set.Icc c d) :
    (∫ u in (0 : ℝ)..1, -Real.log |x - (chart c d u)⁻¹|)
      = -Real.log x + (logCap c d + Real.log ((c + d + 2 * Real.sqrt (c * d)) / 4)) := by
  calc
    (∫ u in (0 : ℝ)..1, -Real.log |x - (chart c d u)⁻¹|)
        = -Real.log x
            + (∫ u in (0 : ℝ)..1, -Real.log |x⁻¹ - chart c d u|)
            + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := split_balay_integral hc hcd hx0
    _ = -Real.log x + (logCap c d + Real.log ((c + d + 2 * Real.sqrt (c * d)) / 4)) := by
          rw [interval_neg_log_abs_chart_sub hcd hw, interval_log_chart hc hcd]
          ring

/-- Algebra: with `c = b⁻¹`, `d = a⁻¹`,
`(c+d+2√(cd))/(d−c) = (a + 2√(ab) + b)/(b − a)`. -/
private lemma sqrt_ab_algebra {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / (a⁻¹ - b⁻¹) =
      (a + 2 * Real.sqrt (a * b) + b) / (b - a) := by
  let q : ℝ := a * b
  have hq : 0 < q := by dsimp [q]; exact mul_pos ha hb
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsqrtq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (le_of_lt hq)
  have hsqinv : Real.sqrt (b⁻¹ * a⁻¹) = (Real.sqrt q)⁻¹ := by
    have hba : b⁻¹ * a⁻¹ = q⁻¹ := by
      dsimp [q]
      field_simp [ha.ne', hb.ne']
    rw [hba, Real.sqrt_inv]
  have hterm : (Real.sqrt q)⁻¹ * q = Real.sqrt q := by
    calc
      (Real.sqrt q)⁻¹ * q = (Real.sqrt q)⁻¹ * (Real.sqrt q * Real.sqrt q) := by rw [hsqrtq]
      _ = Real.sqrt q := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsq), one_mul]
  have hbq : b⁻¹ * (a * b) = a := by
    field_simp [ha.ne', hb.ne']
  have haq : a⁻¹ * (a * b) = b := by
    field_simp [ha.ne', hb.ne']
  have hnum : (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) * q = a + b + 2 * Real.sqrt q := by
    calc
      (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) * q
          = b⁻¹ * q + a⁻¹ * q + 2 * Real.sqrt (b⁻¹ * a⁻¹) * q := by ring
      _ = a + b + 2 * Real.sqrt q := by
            rw [hsqinv]
            rw [mul_assoc]
            rw [hterm]
            dsimp [q]
            rw [hbq, haq]
  have hden : (a⁻¹ - b⁻¹) * q = b - a := by
    calc
      (a⁻¹ - b⁻¹) * q = a⁻¹ * q - b⁻¹ * q := by ring
      _ = b - a := by
            dsimp [q]
            rw [haq, hbq]
  have hcd' : b⁻¹ < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  have hY : a⁻¹ - b⁻¹ ≠ 0 := ne_of_gt (sub_pos.mpr hcd')
  have hD : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hC : (a + b + 2 * Real.sqrt q) = (a + 2 * Real.sqrt (a * b) + b) := by
    dsimp [q]
    ring
  calc
    (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / (a⁻¹ - b⁻¹)
        = (a + b + 2 * Real.sqrt q) / (b - a) := by
            rw [div_eq_div_iff hY hD]
            calc
              (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) * (b - a)
                  = (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) * ((a⁻¹ - b⁻¹) * q) := by rw [hden]
              _ = ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) * q) * (a⁻¹ - b⁻¹) := by ring
              _ = (a + b + 2 * Real.sqrt q) * (a⁻¹ - b⁻¹) := by rw [hnum]
    _ = (a + 2 * Real.sqrt (a * b) + b) / (b - a) := by
            rw [hC]

/-- `U^ν(x) + log‖x‖ = log((a+2√(ab)+b)/(b−a))` for `0 < a < b`, `x ∈ [a,b]`. -/
theorem balay_potential_on_Icc {a b x : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    logPotential (nu a b) (x : ℂ) + Real.log ‖(x : ℂ)‖ =
      Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) := by
  have hb : 0 < b := lt_trans ha hab
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hcb : 0 < (b⁻¹ : ℝ) := inv_pos.mpr hb
  have hcda : (b⁻¹ : ℝ) < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  have hw : x⁻¹ ∈ Set.Icc (b⁻¹) (a⁻¹) :=
    ⟨(inv_le_inv₀ hb hx0).mpr hx.2, (inv_le_inv₀ hx0 ha).mpr hx.1⟩
  -- logPotential (nu a b) (x:ℂ) as an integral over the chart parameter
  have hmeas : Measurable fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖ := by
    fun_prop
  have hfm : AEStronglyMeasurable (fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖)
      (Measure.map (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01) :=
    hmeas.aestronglyMeasurable
  have hchartint := NuChart.nu_integral_eq_chart (a := a) (b := b)
      (f := fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖) hfm
  have hpot : logPotential (nu a b) (x : ℂ)
      = (∫ u : ℝ, -Real.log ‖(x : ℂ) - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖ ∂uniform01) := by
    unfold logPotential
    rw [hchartint]
  have hreal : (fun u : ℝ => -Real.log ‖(x : ℂ) - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖)
      = fun u : ℝ => -Real.log |x - (chart (b⁻¹) (a⁻¹) u)⁻¹| := by
    funext u
    exact log_norm_sub_ofReal x ((chart (b⁻¹) (a⁻¹) u)⁻¹)
  have hii : (∫ u : ℝ, -Real.log |x - (chart (b⁻¹) (a⁻¹) u)⁻¹| ∂uniform01)
      = (∫ u in (0 : ℝ)..1, -Real.log |x - (chart (b⁻¹) (a⁻¹) u)⁻¹|) := by
    exact uniform01_integral (fun u : ℝ => -Real.log |x - (chart (b⁻¹) (a⁻¹) u)⁻¹|)
  have hgen := balay_integral_eq (c := b⁻¹) (d := a⁻¹) (x := x) hcb hcda hx0 hw
  -- value of log ‖(x:ℂ)‖
  have hnorm : Real.log ‖(x : ℂ)‖ = Real.log x := by
    have : ‖(x : ℂ)‖ = x := by
      rw [norm_complex_ofReal]
      exact abs_of_pos hx0
    rw [this]
  calc
    logPotential (nu a b) (x : ℂ) + Real.log ‖(x : ℂ)‖
        = (∫ u in (0 : ℝ)..1, -Real.log |x - (chart (b⁻¹) (a⁻¹) u)⁻¹|)
            + Real.log ‖(x : ℂ)‖ := by
            rw [hpot, hreal, hii]
    _ = (-Real.log x
          + (logCap (b⁻¹) (a⁻¹) + Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4)))
        + Real.log ‖(x : ℂ)‖ := by
            rw [hgen]
    _ = logCap (b⁻¹) (a⁻¹) + Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) := by
            rw [hnorm]
            ring
    _ = Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) := by
            have hcap : logCap (b⁻¹) (a⁻¹) = -Real.log ((a⁻¹ - b⁻¹) / 4) := rfl
            rw [hcap]
            have hcd'' : 0 < a⁻¹ - b⁻¹ := sub_pos.mpr hcda
            have hXpos : 0 < b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹) := by
              have hsq : 0 ≤ Real.sqrt (b⁻¹ * a⁻¹) := Real.sqrt_nonneg _
              nlinarith [hcb, inv_pos.mpr ha, hsq]
            have hfrac : (((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) /
                  ((a⁻¹ - b⁻¹) / 4)) =
                (b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / (a⁻¹ - b⁻¹) := by
              field_simp [ne_of_gt hcd'']
            calc
              -Real.log ((a⁻¹ - b⁻¹) / 4)
                    + Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4)
                  = Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4)
                      - Real.log ((a⁻¹ - b⁻¹) / 4) := by ring
              _ = Real.log (((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) /
                    ((a⁻¹ - b⁻¹) / 4)) := by
                    exact (Real.log_div (div_ne_zero (ne_of_gt hXpos) (by norm_num))
                      (div_ne_zero (ne_of_gt hcd'') (by norm_num))).symm
              _ = Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / (a⁻¹ - b⁻¹)) := by
                    rw [hfrac]
              _ = Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) := by
                    rw [sqrt_ab_algebra ha hb hab]

end Submission.BalayOnIcc
