import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law

/-!
# The first moment of `t ↦ e^{-t}` under the standard exponential law

`expLaw = expMeasure 1` is the standard (rate `1`) exponential law, whose density on `[0,∞)` is
`e^{-t}`.  Hence

  `∫ t, e^{-t} ∂expLaw = ∫_0^∞ e^{-2t} dt = 1/2`.

This is the basic input `E[e^{-E}] = 1/2` for a standard exponential `E`.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory ProbabilityTheory

theorem exp_integral_neg : (∫ t : ℝ, Real.exp (-t) ∂expLaw) = 1/2 := by
  -- `expLaw` is the gamma measure of shape `1` and rate `1`, i.e. `volume.withDensity (gammaPDF 1 1)`.
  have hlaw : expLaw = volume.withDensity (gammaPDF 1 1) := by
    rw [expLaw, expMeasure, gammaMeasure]
  -- On `[0,∞)` the density is `e^{-t}` and it vanishes on the negative half-line.
  have hgamma : ∀ t : ℝ, (gammaPDF 1 1 t).toReal = if 0 ≤ t then Real.exp (-t) else 0 := by
    intro t
    rw [gammaPDF_eq]
    by_cases h : 0 ≤ t
    · rw [if_pos h, if_pos h, ENNReal.toReal_ofReal (by positivity)]
      simp [Real.Gamma_one]
    · rw [if_neg h, if_neg h, ENNReal.toReal_ofReal le_rfl]
  rw [hlaw, integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 1)
        (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1))
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  -- Rewrite the integrand as the indicator of `[0,∞)` of `t ↦ e^{-t} · e^{-t}`.
  have hfun : (fun t : ℝ => (gammaPDF 1 1 t).toReal * Real.exp (-t))
      = (Set.Ici (0:ℝ)).indicator (fun t => Real.exp (-t) * Real.exp (-t)) := by
    funext t
    rw [hgamma t]
    by_cases h : 0 ≤ t
    · rw [if_pos h, Set.indicator_of_mem (Set.mem_Ici.mpr h)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa using h), zero_mul]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  -- `e^{-t} · e^{-t} = e^{-2t}`, and `∫_0^∞ e^{-2t} dt = (1/2)^1 · Γ(1) = 1/2`.
  have hcongr : (fun t : ℝ => Real.exp (-t) * Real.exp (-t)) = fun t => Real.exp (-(2*t)) := by
    funext t
    rw [← Real.exp_add]
    ring_nf
  rw [hcongr]
  have hint := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1:ℝ)) (r := 2) one_pos
    (by norm_num : (0:ℝ) < 2)
  simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] at hint
  exact hint

end Work.ChenPlan.LinearSieve.Selberg.Alt
