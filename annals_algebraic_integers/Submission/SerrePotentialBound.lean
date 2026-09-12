import Submission.PotentialDefs
import Submission.Serre
import Submission.SerreExample
import Submission.SerreMean
import Submission.SupportConcentration
import Submission.BalayPotentialBound
import Submission.EquilibriumPotentialBound
import Submission.NuChart
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Potential bound of the Serre combination (contract A3)

Proves `Submission.SerrePotentialBound.serre_potential_bound`: for `z ≠ 0`,

    logPotential (serreMeasure gSerre aSerre bSerre) z + gSerre·log‖z‖ ≤ serreConstant

where `serreConstant = −log((b−a)/4) + gSerre·log((a+2√(ab)+b)/4)`,
`a = aSerre`, `b = bSerre`, `gSerre = 0.215485`.

## Route

1. **Linearity of the potential.**  `serreMeasure γ a b =
   ofReal γ • nu a b + ofReal (1−γ) • equilibrium a b` and
   `logPotential μ z = ∫ t, −log‖z − (t:ℂ)‖ ∂μ`; expanding by
   `integral_add_measure` and `integral_smul_measure` (ENNReal scalar, with
   `toReal_ofReal`) gives (for integrable log-norm integrand):

       logPotential (serreMeasure γ a b) z
           = γ·logPotential (nu a b) z + (1−γ)·logPotential (equilibrium a b) z.

   The integrand `t ↦ −log‖z − (t:ℂ)‖` is `Integrable` against `nu a b` and
   `equilibrium a b` (for `0 < a < b` and every complex `z`): both measures
   are pushforwards of `uniform01` under the real-analytic chart
   (`equilibrium c d = map (chart c d) uniform01`,
   `nu a b = map (fun u => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01`), and the
   pulled-back integrands are interval integrable on `[0,1]` — continuous with
   a single integrable `log|·|` singularity when `z` is real, handled by
   `MeromorphicOn.intervalIntegrable_log` and the change-of-variables `ae`
   identities for `z − (chart u)⁻¹`.

2. **Bound each piece** (global A1 and A2, both already proved):
   `logPotential (equilibrium a b) z ≤ logCap a b = −log((b−a)/4)`
   (`EquilibriumPotentialBound.equilibrium_potential_bound`);
   `logPotential (nu a b) z ≤ log((a+2√(ab)+b)/(b−a)) − log‖z‖`
   (`BalayPotentialBound.balay_potential_bound`, z ≠ 0).

3. **Constant identity** (pure algebra):
       γ·log((a+2√(ab)+b)/(b−a)) + (1−γ)·(−log((b−a)/4)) + γ·log‖z‖
         = −log((b−a)/4) + γ·log((a+2√(ab)+b)/4)   (the `log‖z‖` cancels),
   i.e. the right-hand side is exactly `serreConstant`.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal Interval

namespace Submission.SerrePotentialBound

open Submission.PotentialDefs
open Submission.Serre
open Submission.SerreExample
open Submission.Equilibrium
open Submission.NuChart

/-! ## Interval integrability of the log-potential integrands

The integrand of the logarithmic potential against the two pushforward
measures, pulled back to the chart parameter `u ∈ (0,1)`.  All the
log-singular integrands are interval integrable: a single `log|·|`
singularity in dimension one is integrable (`MeromorphicOn.intervalIntegrable_log`),
and where `z.im ≠ 0` the integrand is bounded and continuous.
-/

/-- Real-log identity for the inversion chart: for `t > 0`, `x·t ≠ 1`,
`−log|x − t⁻¹| = log t − log|x·t − 1|`. -/
private lemma log_inv_real_eq (x t : ℝ) (hc : 0 < t) (hne : x * t ≠ 1) :
    -Real.log ‖(x : ℂ) - (((t)⁻¹ : ℝ) : ℂ)‖ =
      Real.log t - Real.log |x * t - 1| := by
  have ht0 : t ≠ 0 := ne_of_gt hc
  have hxm : x - t⁻¹ = (x * t - 1) * t⁻¹ := by
    field_simp [ht0]
  have hEq : |x - t⁻¹| = |x * t - 1| * t⁻¹ := by
    calc
      |x - t⁻¹| = |(x * t - 1) * t⁻¹| := by rw [hxm]
      _ = |x * t - 1| * |t⁻¹| := abs_mul (x * t - 1) t⁻¹
      _ = |x * t - 1| * t⁻¹ := by rw [abs_of_pos (inv_pos.mpr hc)]
  have hnorm : ‖(x : ℂ) - ((t⁻¹ : ℝ) : ℂ)‖ = |x - t⁻¹| := by
    rw [← Complex.ofReal_sub, norm_complex_ofReal]
  have hneabs : |x * t - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hlog : Real.log |x - t⁻¹| = Real.log |x * t - 1| - Real.log t := by
    calc
      Real.log |x - t⁻¹| = Real.log (|x * t - 1| * t⁻¹) := by rw [hEq]
      _ = Real.log |x * t - 1| + Real.log (t⁻¹) := Real.log_mul hneabs (inv_ne_zero ht0)
      _ = Real.log |x * t - 1| - Real.log t := by rw [Real.log_inv]; ring
  calc
    -Real.log ‖(x : ℂ) - ((t⁻¹ : ℝ) : ℂ)‖ = -Real.log |x - t⁻¹| := by rw [hnorm]
    _ = -(Real.log |x * t - 1| - Real.log t) := by rw [hlog]
    _ = Real.log t - Real.log |x * t - 1| := by ring

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

/-- Interval integrability on `[0,1]` of `u ↦ log|x·chart c d u − 1|`
(log-singular where the chart meets `x⁻¹`). -/
private lemma log_abs_mul_chart_integrable (c d x : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log |x * chart c d u - 1|) volume (0 : ℝ) 1 := by
  have hf : MeromorphicOn (fun u : ℝ => x * chart c d u - 1) [[(0 : ℝ), 1]] := by
    unfold chart
    apply AnalyticOnNhd.meromorphicOn
    intro x' hx'
    fun_prop
  have hl := hf.intervalIntegrable_log
  convert hl using 1
  · funext u
    rw [Real.log_abs]
    rfl

/-- Interval integrability on `[0,1]` of `u ↦ −log‖w − (chart c d u : ℂ)‖`
for a complex point `w` (log-singular only when `w` is real and the chart hits
it). -/
private lemma intervalIntegrable_z_sub (c d : ℝ) (w : ℂ) :
    IntervalIntegrable (fun u : ℝ => -Real.log ‖w - (chart c d u : ℂ)‖) volume (0 : ℝ) 1 := by
  by_cases hwim : w.im ≠ 0
  · have hne (u : ℝ) : ‖w - (chart c d u : ℂ)‖ ≠ 0 := by
      intro hw0
      have hEq0 : w - (chart c d u : ℂ) = 0 := Complex.norm_eq_zero_iff.mp hw0
      have hIm : (w - (chart c d u : ℂ)).im = 0 := by rw [hEq0]; simp
      exact hwim (by simpa using hIm)
    have hcont : Continuous fun u : ℝ => w - (chart c d u : ℂ) := by
      exact continuous_const.sub (Complex.continuous_ofReal.comp (chart_continuous c d))
    have hnormcont : Continuous fun u : ℝ => ‖w - (chart c d u : ℂ)‖ := by
      exact continuous_norm.comp hcont
    have hlogcont : Continuous fun u : ℝ => Real.log ‖w - (chart c d u : ℂ)‖ := by
      refine Continuous.log (f := fun u : ℝ => ‖w - (chart c d u : ℂ)‖) hnormcont hne
    exact hlogcont.neg.intervalIntegrable (0 : ℝ) 1
  · have hwim0 : w.im = 0 := by
      by_contra h
      exact hwim h
    have hfun : (fun u : ℝ => -Real.log ‖w - (chart c d u : ℂ)‖) =
        fun u : ℝ => -Real.log |w.re - chart c d u| := by
      have hw : w = (w.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hwim0]
      funext u
      apply congrArg Neg.neg
      apply congrArg Real.log
      rw [hw]
      rw [← Complex.ofReal_sub]
      exact norm_complex_ofReal (w.re - chart c d u)
    rw [hfun]
    exact (log_abs_chart_integrable c d w.re).neg

/-- For a real point `x`, interval integrability of the `ν`-chart pullback
`u ↦ −log‖(x:ℂ) − (chart c d u)⁻¹‖` on `[0,1]`: the inversion splits off a
`log(chart u)` term and leaves a single `log|·|` singularity of
`x·chart u − 1`. -/
private lemma intervalIntegrable_inv_chart_z_real (c d x : ℝ) (hc : 0 < c) (hcd : c < d) :
    IntervalIntegrable (fun u : ℝ => -Real.log ‖(x : ℂ) - (((chart c d u)⁻¹ : ℝ) : ℂ)‖) volume (0 : ℝ) 1 := by
  let I : ℝ → ℝ := fun u => -Real.log ‖(x : ℂ) - (((chart c d u)⁻¹ : ℝ) : ℂ)‖
  let S : ℝ → ℝ := fun u => Real.log (chart c d u) - Real.log |x * chart c d u - 1|
  have hS : IntervalIntegrable S volume (0 : ℝ) 1 := by
    have hlogabs := log_abs_mul_chart_integrable c d x
    have h2 : IntervalIntegrable (fun u : ℝ => -Real.log |x * chart c d u - 1|) volume (0 : ℝ) 1 := hlogabs.neg
    have h1 := log_chart_integrable hc (le_of_lt hcd)
    have hsum : IntervalIntegrable (fun u : ℝ => Real.log (chart c d u) + -Real.log |x * chart c d u - 1|) volume (0 : ℝ) 1 :=
      IntervalIntegrable.add h1 h2
    convert hsum using 1
    funext u
    ring
  have hae : I =ᵐ[volume.restrict (Ι (0 : ℝ) 1)] S := by
    change ∀ᵐ u ∂(volume.restrict (Ι (0 : ℝ) 1)), I u = S u
    rw [ae_restrict_iff' measurableSet_uIoc]
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ x * chart c d u = 1}) ?_ ?_
    · intro u hu
      dsimp at hu
      push Not at hu
      rcases hu with ⟨huI, hne⟩
      have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa using huI
      have hcu : 0 < chart c d u := by
        have hmem := chart_mem_Icc (le_of_lt hcd) u
        exact lt_of_lt_of_le hc hmem.1
      refine ⟨huIoc, ?_⟩
      by_contra hchart
      apply hne
      dsimp [I, S]
      exact log_inv_real_eq x (chart c d u) hcu hchart
    · have hnullset : (volume : Measure ℝ) {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ x * chart c d u = 1} = 0 := by
        by_cases hx : x = 0
        · have hset : {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ x * chart c d u = 1} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro u hu
            rcases hu with ⟨huI, huEq⟩
            rw [(by simp [hx] : x * chart c d u = 0)] at huEq
            norm_num at huEq
          rw [hset]
          simp
        · have hseteq : {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ x * chart c d u = 1} =
              {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ chart c d u = x⁻¹} := by
            apply Set.ext
            intro u
            constructor
            · intro hu
              refine ⟨hu.1, ?_⟩
              have hx0 : x ≠ 0 := hx
              have hmain : chart c d u = x⁻¹ := by
                apply mul_left_cancel₀ hx0
                calc
                  x * chart c d u = 1 := hu.2
                  _ = x * x⁻¹ := by field_simp [hx0]
              exact hmain
            · intro hu
              refine ⟨hu.1, ?_⟩
              rw [hu.2]
              field_simp [hx]
          rw [hseteq]
          exact preimage_chart_meas_zero (c := c) (d := d) (w := x⁻¹) hcd
      exact hnullset
  exact (intervalIntegrable_congr_ae hae).mpr hS

/-- Interval integrability on `[0,1]` of the `ν`-chart pullback
`u ↦ −log‖z − (chart c d u)⁻¹‖` for every complex `z` (chart positive on
`[c,d]`, `0 < c < d`). -/
private lemma intervalIntegrable_inv_chart_z (c d : ℝ) (hc : 0 < c) (hcd : c < d) (z : ℂ) :
    IntervalIntegrable (fun u : ℝ => -Real.log ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖) volume (0 : ℝ) 1 := by
  by_cases hz : z.im = 0
  · have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [hzreal]
    exact intervalIntegrable_inv_chart_z_real c d z.re hc hcd
  · have hchart_pos : ∀ u : ℝ, 0 < chart c d u := by
      intro u
      have hmem := chart_mem_Icc (le_of_lt hcd) u
      exact lt_of_lt_of_le hc hmem.1
    have hne (u : ℝ) : ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖ ≠ 0 := by
      intro hw0
      have hEq0 : z - (((chart c d u)⁻¹ : ℝ) : ℂ) = 0 := Complex.norm_eq_zero_iff.mp hw0
      have hIm : (z - (((chart c d u)⁻¹ : ℝ) : ℂ)).im = 0 := by rw [hEq0]; simp
      exact (by simpa using hz : z.im ≠ 0) (by simpa using hIm)
    have hchart_inv : Continuous (fun u : ℝ => ((chart c d u)⁻¹ : ℝ)) := by
      exact (chart_continuous c d).inv₀ (fun u => ne_of_gt (hchart_pos u))
    have hcont : Continuous fun u : ℝ => z - (((chart c d u)⁻¹ : ℝ) : ℂ) := by
      exact continuous_const.sub (Complex.continuous_ofReal.comp hchart_inv)
    have hnormcont : Continuous fun u : ℝ => ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖ := by
      exact continuous_norm.comp hcont
    have hlogcont : Continuous fun u : ℝ => Real.log ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖ := by
      refine Continuous.log (f := fun u : ℝ => ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖) hnormcont hne
    exact hlogcont.neg.intervalIntegrable (0 : ℝ) 1

/-! ## Measure-level integrability

Both `equilibrium c d` and `nu a b` are pushforwards of `uniform01` under
measurable maps, so interval integrability of the pulled-back integrand
transports to `Integrable` of the log-potential integrand.
-/

/-- The log-potential integrand of a complex point. -/
private def integrand (z : ℂ) : ℝ → ℝ := fun t => -Real.log ‖z - (t : ℂ)‖

private lemma integrand_measurable (z : ℂ) : Measurable (integrand z) := by
  change Measurable (fun t : ℝ => -Real.log ‖z - (t : ℂ)‖)
  fun_prop

/-- An interval-integrable function on `[0,1]` is integrable against `uniform01`. -/
private lemma interval_integrable_to_uniform01 {f : ℝ → ℝ} (hII : IntervalIntegrable f volume (0 : ℝ) 1) :
    Integrable f uniform01 := by
  have hIntOn : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := by
    have h := (intervalIntegrable_iff.mp hII)
    simpa [Set.uIoc] using h
  rw [uniform01]
  simpa [IntegrableOn] using hIntOn

/-- `t ↦ −log‖z − t‖` is integrable against the equilibrium measure of any
interval `[c,d]`. -/
private lemma integrable_equilibrium {c d : ℝ} (z : ℂ) :
    Integrable (integrand z) (equilibrium c d) := by
  have hIntU : Integrable (fun u : ℝ => integrand z (chart c d u)) uniform01 := by
    apply interval_integrable_to_uniform01
    change IntervalIntegrable (fun u : ℝ => -Real.log ‖z - (chart c d u : ℂ)‖) volume (0 : ℝ) 1
    exact intervalIntegrable_z_sub c d z
  rw [equilibrium]
  exact (integrable_map_measure (hg := (integrand_measurable z).aestronglyMeasurable)
    (hf := (chart_measurable c d).aemeasurable)).2 hIntU

/-- `t ↦ −log‖z − t‖` is integrable against Serre's measure `ν` on `[a,b]`
(for `0 < a < b`). -/
private lemma integrable_nu {a b : ℝ} (ha : 0 < a) (hab : a < b) (z : ℂ) :
    Integrable (integrand z) (nu a b) := by
  have hb : 0 < b := lt_trans ha hab
  have hcb : 0 < (b⁻¹ : ℝ) := inv_pos.mpr hb
  have hcda : (b⁻¹ : ℝ) < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  have hIntU : Integrable (fun u : ℝ => integrand z (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ))) uniform01 := by
    apply interval_integrable_to_uniform01
    change IntervalIntegrable (fun u : ℝ => -Real.log ‖z - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖)
      volume (0 : ℝ) 1
    exact intervalIntegrable_inv_chart_z (b⁻¹) (a⁻¹) hcb hcda z
  rw [nu_eq_map_inv_chart a b]
  exact (integrable_map_measure (hg := (integrand_measurable z).aestronglyMeasurable)
    (hf := (invChart_measurable a b).aemeasurable)).2 hIntU

/-! ## Linearity of the logarithmic potential (step 1) -/

/-- `logPotential` is affine in the measure argument on Serre's convex
combination: `logPotential (serreMeasure γ a b) z =
γ·logPotential (nu a b) z + (1−γ)·logPotential (equilibrium a b) z`. -/
private lemma logPotential_serreMeasure {γ a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (z : ℂ) :
    logPotential (serreMeasure γ a b) z =
      γ * logPotential (nu a b) z + (1 - γ) * logPotential (equilibrium a b) z := by
  have hInt_nu : Integrable (integrand z) (nu a b) := integrable_nu ha hab z
  have hInt_eq : Integrable (integrand z) (equilibrium a b) := integrable_equilibrium z
  have hInt_nu_s : Integrable (integrand z) (ENNReal.ofReal γ • nu a b) :=
    hInt_nu.smul_measure ENNReal.ofReal_ne_top
  have hInt_eq_s : Integrable (integrand z) (ENNReal.ofReal (1 - γ) • equilibrium a b) :=
    hInt_eq.smul_measure ENNReal.ofReal_ne_top
  unfold logPotential serreMeasure
  change (∫ t : ℝ, integrand z t ∂(ENNReal.ofReal γ • nu a b + ENNReal.ofReal (1 - γ) • equilibrium a b)) =
      γ * (∫ t : ℝ, integrand z t ∂nu a b) + (1 - γ) * (∫ t : ℝ, integrand z t ∂equilibrium a b)
  rw [MeasureTheory.integral_add_measure hInt_nu_s hInt_eq_s]
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal hγ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hγ1)]
  ring

/-! ## Constant identity (step 3) -/

/-- Pure log-algebra: with `A = a + 2√(ab) + b`,
`γ·log(A/(b−a)) + (1−γ)·logCap a b = −log((b−a)/4) + γ·log(A/4)`. -/
private lemma const_identity {a b γ : ℝ} (ha : 0 < a) (hab : a < b) :
    γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) + (1 - γ) * logCap a b =
      -Real.log ((b - a) / 4) + γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
  let A : ℝ := a + 2 * Real.sqrt (a * b) + b
  have hbma : 0 < b - a := sub_pos.mpr hab
  have hA : 0 < A := by
    dsimp [A]
    have hsq : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
    nlinarith [ha]
  have hbma4 : 0 < (b - a) / 4 := by positivity
  have hA4 : 0 < A / 4 := by positivity
  have hrel : Real.log (A / (b - a)) = Real.log (A / 4) - Real.log ((b - a) / 4) := by
    have hlogdiv := Real.log_div (ne_of_gt hA4) (ne_of_gt hbma4)
    rw [← hlogdiv]
    congr 1
    field_simp
  calc
    γ * Real.log (A / (b - a)) + (1 - γ) * logCap a b
        = γ * (Real.log (A / 4) - Real.log ((b - a) / 4)) + (1 - γ) * (-Real.log ((b - a) / 4)) := by
            rw [hrel]
            rfl
    _ = -Real.log ((b - a) / 4) + γ * Real.log (A / 4) := by ring
    _ = -Real.log ((b - a) / 4) + γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
            rfl

/-! ## Assembly (steps 2 and 3) -/

/-- The potential bound for the generic Serre combination
`0 < a < b`, `0 ≤ γ ≤ 1`, `z ≠ 0`:
`U^μ(z) + γ·log‖z‖ ≤ −log((b−a)/4) + γ·log((a+2√(ab)+b)/4)`. -/
private lemma serre_combination_bound {a b γ : ℝ} (ha : 0 < a) (hab : a < b)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {z : ℂ} (hz : z ≠ 0) :
    logPotential (serreMeasure γ a b) z + γ * Real.log ‖z‖ ≤
      -Real.log ((b - a) / 4) + γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
  have hlin := logPotential_serreMeasure (γ := γ) (a := a) (b := b) ha hab hγ0 hγ1 z
  have hbal := Submission.BalayPotentialBound.balay_potential_bound (a := a) (b := b) ha hab hz
  have heq := Submission.EquilibriumPotentialBound.equilibrium_potential_bound (c := a) (d := b) hab z
  calc
    logPotential (serreMeasure γ a b) z + γ * Real.log ‖z‖
        = (γ * logPotential (nu a b) z + (1 - γ) * logPotential (equilibrium a b) z) + γ * Real.log ‖z‖ := by
            rw [hlin]
    _ = γ * (logPotential (nu a b) z + Real.log ‖z‖) + (1 - γ) * logPotential (equilibrium a b) z := by
            ring
    _ ≤ γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) + (1 - γ) * logCap a b := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hbal hγ0)
              (mul_le_mul_of_nonneg_left heq (sub_nonneg.mpr hγ1))
    _ = -Real.log ((b - a) / 4) + γ * Real.log ((a + 2 * Real.sqrt (a * b) + b) / 4) := by
            exact const_identity ha hab

/-- (A3) `U^μ(z) + γ·log‖z‖ ≤ serreConstant` for `z ≠ 0`. -/
theorem serre_potential_bound {z : ℂ} (hz : z ≠ 0) :
    logPotential (serreMeasure gSerre aSerre bSerre) z +
        gSerre * Real.log ‖z‖ ≤ serreConstant := by
  have h := serre_combination_bound (γ := gSerre) (a := aSerre) (b := bSerre)
      aSerre_pos a_lt_b (le_of_lt gSerre_pos) gSerre_le_one hz
  unfold serreConstant
  simpa using h

end Submission.SerrePotentialBound
