import Submission.NuChart
import Submission.ChartLogMoment
import Submission.EquilibriumPotentialBound
import Submission.EquilibriumPotentialIcc
import Submission.PotentialDefs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Balayage bound for all complex z ≠ 0 (contract A2)

Proves `SerreArithmetic.balay_potential_bound`: for `0 < a < b` and `z ≠ 0`,

    logPotential (nu a b) z + Real.log ‖z‖ ≤ log((a + 2√(a·b) + b) / (b − a)).

## Route (complex version of the A2′ argument; A1-global already proved)

With `c := 1/b`, `d := 1/a` (so `[c,d]` is the reciprocal interval) and
`eq := equilibrium c d`:

1. Change variables (`NuChart.nu_integral_eq_chart`), so with `t := chart c d u
   > 0` on `(0,1)` and real-log algebra valid for COMPLEX z ≠ 0:
   `‖z − t⁻¹‖ = ‖z‖·‖t − z⁻¹‖ / t` (pure modulus algebra; `t > 0`), giving
   `−log‖z − t⁻¹‖ + log‖z‖ = −log‖t − z⁻¹‖ + log t`
   (use `‖z‖·‖z⁻¹‖ = 1`, `log_mul`/`log_div` with positivity).
2. Hence (splitting over the `u`-integral as in A2′, `BalayOnIcc`):
       logPotential (nu a b) z + Real.log ‖z‖
           = logPotential (equilibrium c d) (z⁻¹) + ∫ u, log (chart c d u) ∂uniform01
   (the first summand is the potential of `eq` at the complex point `z⁻¹`;
   the second is the log-moment).
3. `∫ u, log (chart c d u) ∂uniform01 = log((c+d+2√(c·d))/4)` by
   `ChartLogMoment.log_moment_chart_eq`.
4. `logPotential (equilibrium c d) (z⁻¹) ≤ logCap c d` by
   `EquilibriumPotentialBound.equilibrium_potential_bound` (global A1) applied
   at the complex point `z⁻¹` (needs only `c < d`).
5. Sum and simplify:
   `logCap c d + log((c+d+2√(cd))/4) = log((c+d+2√(cd))/(d−c))`
   and with `c = 1/b`, `d = 1/a` the algebra
   `(c+d+2√(cd))/(d−c) = (a + 2√(ab) + b)/(b−a)`.

For the change-of-variable/integrability details mirror the (real) proof in
`Submission/BalayOnIcc.lean` (its lemmas are private, so restate them here);
`AEStronglyMeasurable` hypotheses are discharged by measurability/continuity
of the integrands off their null singular set.
-/

noncomputable section

open MeasureTheory
open scoped Real Interval

namespace Submission.BalayPotentialBound

open Submission.NuChart
open Submission.ChartLogMoment
open Submission.EquilibriumPotentialBound
open Submission.PotentialDefs
open Submission.Equilibrium
open Submission.Serre

/-! ## Small helpers (restated from the real proof modules) -/

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

/-- The set of parameters where the chart hits a fixed COMPLEX point has
volume zero: if the point is non-real the set is empty, otherwise it is the
preimage of a single real value. -/
private lemma preimage_chart_complex_meas_zero {c d : ℝ} (hcd : c < d) (w : ℂ) :
    (volume : Measure ℝ) {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ (chart c d u : ℂ) = w} = 0 := by
  by_cases hw : w.im ≠ 0
  · have hempty : {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ (chart c d u : ℂ) = w} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have him : (chart c d u : ℂ).im = 0 := by simp
      have hwim : w.im ≠ 0 := hw
      have : w ≠ (chart c d u : ℂ) := by
        intro hEq
        have : w.im = (chart c d u : ℂ).im := by rw [hEq]
        exact hwim (by simpa [him] using this)
      exact this hu.2.symm
    rw [hempty]
    simp
  · have hwim0 : w.im = 0 := by
      push Not at hw
      exact hw
    have hreal : w = (w.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hwim0]
    have hEqSet : {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ (chart c d u : ℂ) = w} =
        {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ chart c d u = w.re} := by
      apply Set.ext
      intro u
      constructor
      · intro hu
        refine ⟨hu.1, ?_⟩
        have hce : (chart c d u : ℂ) = (w.re : ℂ) := by
          exact hu.2.trans hreal
        exact Complex.ofReal_inj.mp hce
      · intro hu
        refine ⟨hu.1, ?_⟩
        rw [hreal]
        exact congrArg (fun r : ℝ => (r : ℂ)) hu.2
    rw [hEqSet]
    exact preimage_chart_meas_zero (c := c) (d := d) (w := w.re) hcd

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

/-! ## The complex change-of-variables algebra -/

/-- Complex-log identity:
`−log‖z − t⁻¹‖ = −log‖z‖ − log‖z⁻¹ − t‖ + log t` for `z ≠ 0`, `t > 0`,
`t ≠ z⁻¹` (complex inverse; equality fails exactly at the chart point hitting
`z⁻¹`). -/
private lemma z_log_inv_norm {z : ℂ} (t : ℝ) (hz : z ≠ 0) (ht : 0 < t)
    (htne : (t : ℂ) ≠ z⁻¹) :
    -Real.log ‖z - (t⁻¹ : ℂ)‖ = -Real.log ‖z‖ - Real.log ‖z⁻¹ - (t : ℂ)‖ + Real.log t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htz1 : (t : ℂ) * (t⁻¹ : ℂ) = 1 := by
    rw [← Complex.ofReal_inv]
    rw [← Complex.ofReal_mul]
    norm_num [mul_inv_cancel₀ ht0]
  have hzz1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have hprod : (t : ℂ) * (z - (t⁻¹ : ℂ)) = z * ((t : ℂ) - z⁻¹) := by
    calc
      (t : ℂ) * (z - (t⁻¹ : ℂ)) = (t : ℂ) * z - (t : ℂ) * (t⁻¹ : ℂ) := by rw [mul_sub]
      _ = z * (t : ℂ) - 1 := by
            rw [htz1]
            ring
      _ = z * ((t : ℂ) - z⁻¹) := by
            rw [mul_sub, ← hzz1]
  have hnorm_t : ‖(t : ℂ)‖ = t := by
    rw [norm_complex_ofReal, abs_of_pos ht]
  have hmain : t * ‖z - (t⁻¹ : ℂ)‖ = ‖z‖ * ‖z⁻¹ - (t : ℂ)‖ := by
    calc
      t * ‖z - (t⁻¹ : ℂ)‖ = ‖(t : ℂ)‖ * ‖z - (t⁻¹ : ℂ)‖ := by rw [hnorm_t]
      _ = ‖(t : ℂ) * (z - (t⁻¹ : ℂ))‖ := (norm_mul (t : ℂ) (z - (t⁻¹ : ℂ))).symm
      _ = ‖z * ((t : ℂ) - z⁻¹)‖ := by rw [hprod]
      _ = ‖z‖ * ‖(t : ℂ) - z⁻¹‖ := norm_mul z ((t : ℂ) - z⁻¹)
      _ = ‖z‖ * ‖z⁻¹ - (t : ℂ)‖ := by
            have hsym : ‖(t : ℂ) - z⁻¹‖ = ‖z⁻¹ - (t : ℂ)‖ :=
              (norm_sub_rev z⁻¹ (t : ℂ)).symm
            rw [hsym]
  have hnormA : ‖z - (t⁻¹ : ℂ)‖ = ‖z‖ * ‖z⁻¹ - (t : ℂ)‖ * t⁻¹ := by
    calc
      ‖z - (t⁻¹ : ℂ)‖ = t⁻¹ * (t * ‖z - (t⁻¹ : ℂ)‖) := by
            rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      _ = t⁻¹ * (‖z‖ * ‖z⁻¹ - (t : ℂ)‖) := by rw [hmain]
      _ = ‖z‖ * ‖z⁻¹ - (t : ℂ)‖ * t⁻¹ := by ring
  have hB0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hC0 : ‖z⁻¹ - (t : ℂ)‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm htne))
  have htin0 : (t⁻¹ : ℝ) ≠ 0 := inv_ne_zero ht0
  have hBC : ‖z‖ * ‖z⁻¹ - (t : ℂ)‖ ≠ 0 := mul_ne_zero hB0 hC0
  have hlogprod : Real.log (‖z‖ * ‖z⁻¹ - (t : ℂ)‖ * t⁻¹) =
      Real.log ‖z‖ + Real.log ‖z⁻¹ - (t : ℂ)‖ + Real.log (t⁻¹) := by
    calc
      Real.log (‖z‖ * ‖z⁻¹ - (t : ℂ)‖ * t⁻¹)
          = Real.log (‖z‖ * ‖z⁻¹ - (t : ℂ)‖) + Real.log (t⁻¹) := Real.log_mul hBC htin0
      _ = (Real.log ‖z‖ + Real.log ‖z⁻¹ - (t : ℂ)‖) + Real.log (t⁻¹) := by
            rw [Real.log_mul hB0 hC0]
  calc
    -Real.log ‖z - (t⁻¹ : ℂ)‖
        = -Real.log (‖z‖ * ‖z⁻¹ - (t : ℂ)‖ * t⁻¹) := by rw [hnormA]
    _ = -(Real.log ‖z‖ + Real.log ‖z⁻¹ - (t : ℂ)‖ + Real.log (t⁻¹)) := by rw [hlogprod]
    _ = -Real.log ‖z‖ - Real.log ‖z⁻¹ - (t : ℂ)‖ + Real.log t := by
          rw [Real.log_inv]
          ring

/-- The balayage integrand equals its algebraic split almost everywhere on
`(0,1]`: `−log‖z − (chart u)⁻¹‖ =
(−log‖z‖) + (−log‖z⁻¹ − chart u‖) + log(chart u)`. -/
private lemma ae_balay_split_z {c d : ℝ} (hc : 0 < c) (hcd : c < d) {z : ℂ} (hz : z ≠ 0) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (0 : ℝ) 1 →
      (-Real.log ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖) =
        ((-Real.log ‖z‖) + (-Real.log ‖z⁻¹ - (chart c d u : ℂ)‖)) + Real.log (chart c d u) := by
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null
  · intro u hu
    dsimp at hu
    push Not at hu
    rcases hu with ⟨huI, hne⟩
    have hchart : (chart c d u : ℂ) = z⁻¹ := by
      by_contra hch
      have ht : 0 < chart c d u := by
        have hmem := chart_mem_Icc (le_of_lt hcd) u
        exact lt_of_lt_of_le hc hmem.1
      have hEq := z_log_inv_norm (z := z) (chart c d u) hz ht hch
      have hsplit : -Real.log ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖ =
          ((-Real.log ‖z‖) + (-Real.log ‖z⁻¹ - (chart c d u : ℂ)‖)) + Real.log (chart c d u) := by
        rw [Complex.ofReal_inv]
        rw [hEq]
        ring
      exact hne hsplit
    show u ∈ Set.Ioc (0 : ℝ) 1 ∧ (chart c d u : ℂ) = z⁻¹
    exact ⟨by simpa using huI, hchart⟩
  · exact preimage_chart_complex_meas_zero (c := c) (d := d) (w := z⁻¹) hcd

/-- Splitting the balayage integral over `u ∈ [0,1]`:
`∫₀¹ −log‖z − (chart u)⁻¹‖ = −log‖z‖ + ∫₀¹ −log‖z⁻¹ − (chart u)‖ + ∫₀¹ log(chart u)`. -/
private lemma split_balay_integral_z {c d : ℝ} (hc : 0 < c) (hcd : c < d) {z : ℂ} (hz : z ≠ 0) :
    (∫ u in (0 : ℝ)..1, -Real.log ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖)
      = -Real.log ‖z‖
          + (∫ u in (0 : ℝ)..1, -Real.log ‖z⁻¹ - (chart c d u : ℂ)‖)
          + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
  let p1 : ℝ → ℝ := fun _ : ℝ => -Real.log ‖z‖
  let p2 : ℝ → ℝ := fun u => -Real.log ‖z⁻¹ - (chart c d u : ℂ)‖
  let p3 : ℝ → ℝ := fun u => Real.log (chart c d u)
  have ip3 : IntervalIntegrable p3 volume (0 : ℝ) 1 := by
    dsimp [p3]
    exact log_chart_integrable hc (le_of_lt hcd)
  have ip2 : IntervalIntegrable p2 volume (0 : ℝ) 1 := by
    dsimp [p2]
    exact intervalIntegrable_z_sub c d z⁻¹
  have ip1 : IntervalIntegrable p1 volume (0 : ℝ) 1 := intervalIntegrable_const
  calc
    (∫ u in (0 : ℝ)..1, -Real.log ‖z - (((chart c d u)⁻¹ : ℝ) : ℂ)‖)
        = (∫ u in (0 : ℝ)..1,
            ((-Real.log ‖z‖) + (-Real.log ‖z⁻¹ - (chart c d u : ℂ)‖)) + Real.log (chart c d u)) := by
            exact intervalIntegral.integral_congr_ae (ae_balay_split_z hc hcd hz)
    _ = (∫ u in (0 : ℝ)..1, p1 u + p2 u)
        + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [intervalIntegral.integral_add (IntervalIntegrable.add ip1 ip2) ip3]
    _ = (∫ u in (0 : ℝ)..1, p1 u)
        + (∫ u in (0 : ℝ)..1, -Real.log ‖z⁻¹ - (chart c d u : ℂ)‖)
        + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [intervalIntegral.integral_add ip1 ip2]
    _ = -Real.log ‖z‖
        + (∫ u in (0 : ℝ)..1, -Real.log ‖z⁻¹ - (chart c d u : ℂ)‖)
        + (∫ u in (0 : ℝ)..1, Real.log (chart c d u)) := by
            rw [intervalIntegral.integral_const]
            simp

/-! ## Relating back to measure-level potentials -/

/-- The equilibrium potential at a complex point, as an interval integral over
the chart parameter `u ∈ [0,1]`. -/
private lemma logPotential_eq_chart_int {c d : ℝ} (w : ℂ) :
    logPotential (equilibrium c d) w = (∫ u in (0 : ℝ)..1, -Real.log ‖w - (chart c d u : ℂ)‖) := by
  unfold logPotential equilibrium
  have h1 : (∫ t : ℝ, -Real.log ‖w - (t : ℂ)‖ ∂Measure.map (chart c d) uniform01) =
      (∫ u : ℝ, -Real.log ‖w - (chart c d u : ℂ)‖ ∂uniform01) := by
    exact MeasureTheory.integral_map (φ := chart c d) (μ := uniform01)
      (f := fun t : ℝ => -Real.log ‖w - (t : ℂ)‖)
      (chart_measurable c d).aemeasurable
      (by
        have hmeas : Measurable fun t : ℝ => -Real.log ‖w - (t : ℂ)‖ := by
          fun_prop
        exact hmeas.aestronglyMeasurable)
  rw [h1]
  exact uniform01_integral (fun u : ℝ => -Real.log ‖w - (chart c d u : ℂ)‖)

/-! ## The final algebra -/

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

/-- `−log((d−c)/4) + log((c+d+2√(cd))/4) = log((a+2√(ab)+b)/(b−a))` at
`c = b⁻¹`, `d = a⁻¹`. -/
private lemma cap_plus_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    logCap (b⁻¹) (a⁻¹) + Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) =
      Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) := by
  have hcda : (b⁻¹ : ℝ) < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  have hcap : logCap (b⁻¹) (a⁻¹) = -Real.log ((a⁻¹ - b⁻¹) / 4) := rfl
  rw [hcap]
  have hcd'' : 0 < a⁻¹ - b⁻¹ := sub_pos.mpr hcda
  have hXpos : 0 < b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹) := by
    have hsq : 0 ≤ Real.sqrt (b⁻¹ * a⁻¹) := Real.sqrt_nonneg _
    nlinarith [inv_pos.mpr hb, inv_pos.mpr ha, hsq]
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

/-- `U^ν(z) + log‖z‖ ≤ log((a+2√(ab)+b)/(b−a))` for `0 < a < b`, `z ≠ 0`. -/
theorem balay_potential_bound {a b : ℝ} (ha : 0 < a) (hab : a < b) {z : ℂ}
    (hz : z ≠ 0) :
    logPotential (nu a b) z + Real.log ‖z‖ ≤
      Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) := by
  have hb : 0 < b := lt_trans ha hab
  have hcb : 0 < (b⁻¹ : ℝ) := inv_pos.mpr hb
  have hcda : (b⁻¹ : ℝ) < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  -- logPotential (nu a b) z as an interval integral over the chart parameter
  have hmeas : Measurable fun t : ℝ => -Real.log ‖z - (t : ℂ)‖ := by
    fun_prop
  have hfm : AEStronglyMeasurable (fun t : ℝ => -Real.log ‖z - (t : ℂ)‖)
      (Measure.map (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01) :=
    hmeas.aestronglyMeasurable
  have hchartint := NuChart.nu_integral_eq_chart (a := a) (b := b)
      (f := fun t : ℝ => -Real.log ‖z - (t : ℂ)‖) hfm
  have hpot : logPotential (nu a b) z
      = (∫ u : ℝ, -Real.log ‖z - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖ ∂uniform01) := by
    unfold logPotential
    rw [hchartint]
  have hii : (∫ u : ℝ, -Real.log ‖z - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖ ∂uniform01)
      = (∫ u in (0 : ℝ)..1, -Real.log ‖z - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖) := by
    exact uniform01_integral (fun u : ℝ => -Real.log ‖z - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖)
  have hsplit := split_balay_integral_z (c := b⁻¹) (d := a⁻¹) hcb hcda hz
  have hK : (∫ u in (0 : ℝ)..1, Real.log (chart (b⁻¹) (a⁻¹) u)) =
      Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) := by
    have hm := log_moment_chart_eq (c := b⁻¹) (d := a⁻¹) hcb hcda
    rw [uniform01_integral] at hm
    exact hm
  have hJ : (∫ u in (0 : ℝ)..1, -Real.log ‖z⁻¹ - (chart (b⁻¹) (a⁻¹) u : ℂ)‖) =
      logPotential (equilibrium (b⁻¹) (a⁻¹)) (z⁻¹) := by
    exact (logPotential_eq_chart_int (c := b⁻¹) (d := a⁻¹) (w := z⁻¹)).symm
  have hJbound : logPotential (equilibrium (b⁻¹) (a⁻¹)) (z⁻¹) ≤ logCap (b⁻¹) (a⁻¹) :=
    equilibrium_potential_bound hcda (z⁻¹)
  calc
    logPotential (nu a b) z + Real.log ‖z‖
        = (∫ u in (0 : ℝ)..1, -Real.log ‖z - (((chart (b⁻¹) (a⁻¹) u)⁻¹ : ℝ) : ℂ)‖)
            + Real.log ‖z‖ := by
            rw [hpot, hii]
    _ = (-Real.log ‖z‖
          + (∫ u in (0 : ℝ)..1, -Real.log ‖z⁻¹ - (chart (b⁻¹) (a⁻¹) u : ℂ)‖)
          + (∫ u in (0 : ℝ)..1, Real.log (chart (b⁻¹) (a⁻¹) u))) + Real.log ‖z‖ := by
            rw [hsplit]
    _ = (∫ u in (0 : ℝ)..1, -Real.log ‖z⁻¹ - (chart (b⁻¹) (a⁻¹) u : ℂ)‖)
          + (∫ u in (0 : ℝ)..1, Real.log (chart (b⁻¹) (a⁻¹) u)) := by
            ring
    _ = logPotential (equilibrium (b⁻¹) (a⁻¹)) (z⁻¹)
          + (∫ u in (0 : ℝ)..1, Real.log (chart (b⁻¹) (a⁻¹) u)) := by
            rw [hJ]
    _ ≤ logCap (b⁻¹) (a⁻¹)
          + (∫ u in (0 : ℝ)..1, Real.log (chart (b⁻¹) (a⁻¹) u)) := by
            exact add_le_add_left hJbound _
    _ = logCap (b⁻¹) (a⁻¹) + Real.log ((b⁻¹ + a⁻¹ + 2 * Real.sqrt (b⁻¹ * a⁻¹)) / 4) := by
            rw [hK]
    _ = Real.log ((a + 2 * Real.sqrt (a * b) + b) / (b - a)) := by
            exact cap_plus_moment ha hb hab

end Submission.BalayPotentialBound
