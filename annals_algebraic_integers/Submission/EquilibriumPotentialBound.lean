import Submission.PotentialDefs
import Submission.EquilibriumMeasure
import Submission.EquilibriumPotentialBoundReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric

/-!
# Global bound of the equilibrium potential (A1, all complex z)

For `c < d` and EVERY `z ∈ ℂ`:

    logPotential (equilibrium c d) z ≤ logCap c d = −log((d−c)/4)

## Route (avoids Joukowski theory: real-axis domination)

1. **Domination by the real axis.**  For real `x` and `z = a + i·y`,
   `‖z − x‖² = ‖(a:ℂ) − x‖² + y² ≥ ‖(a:ℂ) − x‖²`, so for `x ≠ a`
   (i.e. except possibly the single point `x = z.re`),
   `‖z − x‖ ≥ ‖(z.re : ℂ) − x‖` and hence (log monotone)
   `−log‖z − x‖ ≤ −log‖(z.re:ℂ) − x‖`.  The exceptional point carries no
   `equilibrium c d` mass (`equilibrium c d` is the pushforward of
   Lebesgue-`uniform01` under the chart, and a single point has Lebesgue
   measure zero, so `equilibrium c d {z.re} = 0`); hence
   `logPotential (equilibrium c d) z ≤ logPotential (equilibrium c d) (z.re : ℂ)`.
2. **Real case.**  By `EquilibriumPotentialBoundReal.equilibrium_potential_bound_real`,
   `logPotential (equilibrium c d) (z.re : ℂ) ≤ logCap c d`.
3. Chain the two inequalities.

In this file the domination is proved in the chart coordinates: both sides
are rewritten as interval integrals in `u ∈ 0..1` over the integrands
`−log‖z − (chart c d u : ℂ)‖` and `−log‖(z.re : ℂ) − (chart c d u : ℂ)‖`.
The pointwise domination holds off the (at most one point) set where the
chart hits `z.re`, so it holds almost everywhere on `[0,1]`; both integrands
are interval integrable (continuity when `z.im ≠ 0`, and the real-meromorphic
log-integrability lemma for the real-axis integrand), and
`intervalIntegral.integral_mono_ae_restrict` closes the comparison.
-/

noncomputable section

open MeasureTheory
open scoped Real Interval

namespace Submission.EquilibriumPotentialBound

open Submission.PotentialDefs
open Submission.Equilibrium
open Submission.EquilibriumPotentialBoundReal

/-! ## Small analytic helpers -/

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

/-- The set of parameters `u ∈ [0,1]` where the chart hits a fixed value has
volume zero (the chart is injective on `[0,1]`). -/
private lemma preimage_chart_Icc_meas_zero {c d w : ℝ} (hcd : c < d) :
    (volume : Measure ℝ) {u | chart c d u = w ∧ u ∈ Set.Icc (0 : ℝ) 1} = 0 := by
  let S : Set ℝ := {u | chart c d u = w ∧ u ∈ Set.Icc (0 : ℝ) 1}
  have hsubsing : S.Subsingleton := by
    intro u hu v hv
    have hInj := (chart_strictAntiOn hcd).injOn
    exact hInj hu.2 hv.2 (by rw [hu.1, hv.1])
  exact hsubsing.measure_zero (volume : Measure ℝ)

/-! ## The pointwise domination off the real axis -/

/-- For every real `x ≠ z.re`: `−log‖z − x‖ ≤ −log‖(z.re:ℂ) − x‖`. -/
private lemma log_dominated_off_re (z : ℂ) (x : ℝ) (hx : x ≠ z.re) :
    -Real.log ‖z - (x : ℂ)‖ ≤ -Real.log ‖(z.re : ℂ) - (x : ℂ)‖ := by
  have hle : ‖(z.re : ℂ) - (x : ℂ)‖ ≤ ‖z - (x : ℂ)‖ := by
    calc
      ‖(z.re : ℂ) - (x : ℂ)‖ = |z.re - x| := by
          rw [← Complex.ofReal_sub]
          rw [norm_complex_ofReal]
      _ ≤ ‖z - (x : ℂ)‖ := by
          simpa using Complex.abs_re_le_norm (z - (x : ℂ))
  have hsmallpos : 0 < ‖(z.re : ℂ) - (x : ℂ)‖ := by
    rw [← Complex.ofReal_sub]
    rw [norm_complex_ofReal]
    exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx))
  have hlog := Real.log_le_log hsmallpos hle
  linarith

/-! ## Interval integrability of the two integrands -/

/-- The integrand for a point off the real axis is continuous (its argument is
bounded below by `|z.im| > 0`), hence interval integrable. -/
private lemma intervalIntegrable_z_ne_im (c d : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    IntervalIntegrable (fun u : ℝ => -Real.log ‖z - (chart c d u : ℂ)‖) volume (0 : ℝ) 1 := by
  have hne (u : ℝ) : ‖z - (chart c d u : ℂ)‖ ≠ 0 := by
    intro hz0
    have hEq0 : z - (chart c d u : ℂ) = 0 := Complex.norm_eq_zero_iff.mp hz0
    have hIm : (z - (chart c d u : ℂ)).im = 0 := by rw [hEq0]; simp
    exact hz (by simpa using hIm)
  have hcont : Continuous fun u : ℝ => z - (chart c d u : ℂ) := by
    exact continuous_const.sub (Complex.continuous_ofReal.comp (chart_continuous c d))
  have hnormcont : Continuous fun u : ℝ => ‖z - (chart c d u : ℂ)‖ := by
    exact continuous_norm.comp hcont
  have hlogcont : Continuous fun u : ℝ => Real.log ‖z - (chart c d u : ℂ)‖ := by
    refine Continuous.log (f := fun u => ‖z - (chart c d u : ℂ)‖) hnormcont hne
  exact hlogcont.neg.intervalIntegrable (0 : ℝ) 1

/-- The real-axis integrand `u ↦ −log‖(a:ℂ) − (chart c d u : ℂ)‖` is interval
integrable: it is `−log` of the absolute value of a real-meromorphic function
(`a − chart`), and logarithms of real-meromorphic functions are interval
integrable (with the log-singularity where the chart meets `a`). -/
private lemma intervalIntegrable_z_re (c d a : ℝ) :
    IntervalIntegrable (fun u : ℝ => -Real.log ‖(a : ℂ) - (chart c d u : ℂ)‖) volume (0 : ℝ) 1 := by
  have hm : MeromorphicOn (fun u : ℝ => a - chart c d u) [[(0 : ℝ), 1]] := by
    unfold chart
    apply AnalyticOnNhd.meromorphicOn
    intro x hx
    fun_prop
  have hlog : IntervalIntegrable (fun u : ℝ => Real.log (a - chart c d u)) volume (0 : ℝ) 1 := by
    exact hm.intervalIntegrable_log
  have hEq : (fun u : ℝ => Real.log (a - chart c d u)) =
      fun u : ℝ => Real.log ‖(a : ℂ) - (chart c d u : ℂ)‖ := by
    funext u
    rw [← Real.log_abs (a - chart c d u)]
    congr 1
    rw [← Complex.ofReal_sub]
    exact (norm_complex_ofReal (a - chart c d u)).symm
  have hlog' : IntervalIntegrable (fun u : ℝ => Real.log ‖(a : ℂ) - (chart c d u : ℂ)‖) volume (0 : ℝ) 1 := by
    simpa [hEq] using hlog
  exact hlog'.neg

/-! ## Almost-everywhere domination on the parameter interval -/

/-- The pointwise domination holds almost everywhere on `[0,1]` (w.r.t. the
restricted Lebesgue measure): it can only fail where the chart hits `z.re`. -/
private lemma ae_dominated_on_Icc {c d : ℝ} (hcd : c < d) (z : ℂ) :
    (fun u : ℝ => -Real.log ‖z - (chart c d u : ℂ)‖) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun u : ℝ => -Real.log ‖(z.re : ℂ) - (chart c d u : ℂ)‖) := by
  change ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
    -Real.log ‖z - (chart c d u : ℂ)‖ ≤ -Real.log ‖(z.re : ℂ) - (chart c d u : ℂ)‖
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null
  · intro u hu
    dsimp at hu
    by_contra hchart
    have hpt := log_dominated_off_re z (chart c d u) hchart
    exact hu hpt
  · have hmeas : MeasurableSet {u : ℝ | chart c d u = z.re} :=
      (chart_measurable c d) (isClosed_singleton.measurableSet)
    calc
      (volume.restrict (Set.Icc (0 : ℝ) 1)) {u : ℝ | chart c d u = z.re}
          = volume ({u : ℝ | chart c d u = z.re} ∩ Set.Icc (0 : ℝ) 1) := by
              rw [Measure.restrict_apply hmeas]
      _ = 0 := by
              simpa [Set.inter_def] using
                preimage_chart_Icc_meas_zero (c := c) (d := d) (w := z.re) hcd

/-! ## The interval-integral comparison and the measure-level rewrite -/

/-- The domination inequality in chart coordinates. -/
private lemma interval_le_of_re {c d : ℝ} (hcd : c < d) (z : ℂ) :
    (∫ u in (0 : ℝ)..1, -Real.log ‖z - (chart c d u : ℂ)‖) ≤
      (∫ u in (0 : ℝ)..1, -Real.log ‖(z.re : ℂ) - (chart c d u : ℂ)‖) := by
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  by_cases hz : z.im = 0
  · have hz' : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hz]
    rw [hz']
    simp
  · have hf : IntervalIntegrable (fun u : ℝ => -Real.log ‖z - (chart c d u : ℂ)‖) volume (0 : ℝ) 1 :=
      intervalIntegrable_z_ne_im c d z hz
    have hg : IntervalIntegrable (fun u : ℝ => -Real.log ‖(z.re : ℂ) - (chart c d u : ℂ)‖) volume (0 : ℝ) 1 :=
      intervalIntegrable_z_re c d z.re
    exact intervalIntegral.integral_mono_ae_restrict (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => -Real.log ‖z - (chart c d u : ℂ)‖)
      (g := fun u : ℝ => -Real.log ‖(z.re : ℂ) - (chart c d u : ℂ)‖)
      hab hf hg (ae_dominated_on_Icc hcd z)

/-- The logarithmic potential, rewritten as an interval integral over the
chart parameter `u ∈ [0,1]`. -/
private lemma logPotential_eq_chart {c d : ℝ} (z : ℂ) :
    logPotential (equilibrium c d) z = (∫ u in (0 : ℝ)..1, -Real.log ‖z - (chart c d u : ℂ)‖) := by
  unfold logPotential equilibrium
  have h1 : (∫ t : ℝ, -Real.log ‖z - (t : ℂ)‖ ∂Measure.map (chart c d) uniform01) =
      (∫ u : ℝ, -Real.log ‖z - (chart c d u : ℂ)‖ ∂uniform01) := by
    exact MeasureTheory.integral_map (φ := chart c d) (μ := uniform01)
      (f := fun t : ℝ => -Real.log ‖z - (t : ℂ)‖)
      (chart_measurable c d).aemeasurable
      (by
        have hmeas : Measurable fun t : ℝ => -Real.log ‖z - (t : ℂ)‖ := by
          fun_prop
        exact hmeas.aestronglyMeasurable)
  rw [h1]
  exact uniform01_integral (fun u : ℝ => -Real.log ‖z - (chart c d u : ℂ)‖)

/-- Domination: moving off the real axis only lowers the potential. -/
lemma potential_le_of_re {c d : ℝ} (hcd : c < d) (z : ℂ) :
    logPotential (equilibrium c d) z ≤ logPotential (equilibrium c d) (z.re : ℂ) := by
  rw [logPotential_eq_chart z, logPotential_eq_chart (z.re : ℂ)]
  exact interval_le_of_re hcd z

/-- (A1) Global bound of the equilibrium potential for all complex `z`. -/
theorem equilibrium_potential_bound {c d : ℝ} (hcd : c < d) (z : ℂ) :
    logPotential (equilibrium c d) z ≤ logCap c d := by
  exact le_trans (potential_le_of_re hcd z) (equilibrium_potential_bound_real (x := z.re) hcd)

end Submission.EquilibriumPotentialBound
