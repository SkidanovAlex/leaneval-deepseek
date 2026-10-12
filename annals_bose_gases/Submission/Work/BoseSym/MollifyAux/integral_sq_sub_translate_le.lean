import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseSym.MollifyAux.integrable_fderiv_sq
import Submission.Work.BoseSym.MollifyAux.lintegral_lintegral_sub_smul
import Submission.Work.BoseSym.MollifyAux.norm_sub_le_integral_fderiv
import Submission.Work.BoseSym.MollifyAux.sq_intervalIntegral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `L²` modulus of continuity of a `C¹` compactly supported function

For `f : Conf N → ℝ` of class `C¹` with compact support and any `y : Conf N`,

`∫ x, (f x - f (x - y))² ≤ ‖y‖² * ∫ x, ‖fderiv ℝ f x‖²` .

This is the `L²` form of the mean value estimate: the displacement along the
segment `[x - y, x]` is the integral of the directional derivative, so

* (pointwise, `norm_sub_le_integral_fderiv`) `‖f x - f (x - y)‖ ≤ ∫ t in 0..1, ‖fderiv ℝ f (x - t • y)‖ * ‖y‖`;
* Cauchy–Schwarz on the unit interval (`sq_intervalIntegral_le`) turns the square
  of that integral into the integral of the square;
* integrating over `x` and interchanging the two integrals
  (`lintegral_lintegral_sub_smul`) reduces the result to the translation
  invariance of Lebesgue measure, the `t`-integral of a constant being its value
  (`volume (Ioc 0 1) = 1`).

The whole argument is carried out at the level of `ℝ≥0∞`-valued lower integrals,
which is where no integrability hypotheses are needed; the two conversions to the
Bochner integral use `integral_eq_lintegral_of_nonneg_ae` and the finiteness of
`∫⁻ x, ofReal ‖fderiv ℝ f x‖²` (`integrable_fderiv_sq`).
-/

namespace Work.BoseSym.MollifyAux

open MeasureTheory
open scoped ENNReal Real
open Work.BoseSym

theorem integral_sq_sub_translate_le {N : ℕ} {f : Conf N → ℝ} (hf : Smooth1 f)
    (hcs : HasCompactSupport f) (y : Conf N) :
    ∫ x, (f x - f (x - y)) ^ 2 ∂(volC N)
      ≤ ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(volC N) := by
  have hfc : Continuous f := hf.continuous
  have hfdc : Continuous fun x : Conf N => fderiv ℝ f x := hf.continuous_fderiv (by norm_num)
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hle1 : (0:ℝ) ≤ 1 := by norm_num
  -- ## The pointwise bound, in `ℝ≥0∞`
  have hpt : ∀ x : Conf N, ENNReal.ofReal ((f x - f (x - y)) ^ 2)
      ≤ ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
          ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1)) := by
    intro x
    have htd : Continuous fun t : ℝ => ‖fderiv ℝ f (x - t • y)‖ :=
      hfdc.norm.comp (by fun_prop : Continuous fun t : ℝ => x - t • y)
    have hV : Continuous fun t : ℝ => ‖fderiv ℝ f (x - t • y)‖ ^ 2 := htd.pow 2
    -- the displacement is at most the integral of the speed
    have h1 : ‖f x - f (x - y)‖ ≤ ‖y‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ := by
      refine (norm_sub_le_integral_fderiv hf x y).trans (le_of_eq ?_)
      exact (intervalIntegral.integral_congr (fun t _ => mul_comm _ _)).trans
        (intervalIntegral.integral_const_mul _ _)
    -- Cauchy–Schwarz on the unit interval
    have hsq : (‖y‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖) ^ 2
        ≤ ‖y‖ ^ 2 * ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (sq_intervalIntegral_le htd) (sq_nonneg ‖y‖)
    have hreal : (f x - f (x - y)) ^ 2
        ≤ ‖y‖ ^ 2 * ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ ^ 2 := by
      calc (f x - f (x - y)) ^ 2 = ‖f x - f (x - y)‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ (‖y‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ _ := hsq
    -- the interval integral, as a lower integral against the restricted measure
    have hInt : Integrable (fun t : ℝ => ‖fderiv ℝ f (x - t • y)‖ ^ 2)
        (Measure.restrict volume (Set.Ioc (0:ℝ) 1)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle1).mp (hV.intervalIntegrable 0 1)
    have hof : ENNReal.ofReal (∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ ^ 2)
        = ∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
            ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1)) := by
      rw [intervalIntegral.integral_of_le hle1]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun t => sq_nonneg _)
    calc ENNReal.ofReal ((f x - f (x - y)) ^ 2)
        ≤ ENNReal.ofReal (‖y‖ ^ 2 * ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (‖y‖ ^ 2) *
            ENNReal.ofReal (∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg _)
      _ = ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
            ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1)) := by
          rw [hof, ENNReal.ofReal_pow hy0]
  -- ## Integration over `x`
  have hHm : Measurable fun z : Conf N => ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hfdc.norm.pow 2).measurable)
  have h2 : ∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N)
      ≤ ∫⁻ x, ENNReal.ofReal ‖y‖ ^ 2 * (∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
          ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1))) ∂(volC N) := lintegral_mono hpt
  have hmeas : Measurable fun x : Conf N => ∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
      ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1)) := by
    have hun : Measurable
        (fun p : Conf N × ℝ => ENNReal.ofReal (‖fderiv ℝ f (p.1 - p.2 • y)‖ ^ 2)) :=
      hHm.comp (by fun_prop : Measurable fun p : Conf N × ℝ => p.1 - p.2 • y)
    exact hun.lintegral_prod_right
  have h3 : ∫⁻ x, ENNReal.ofReal ‖y‖ ^ 2 * (∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
        ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1))) ∂(volC N)
      = ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ x, (∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
        ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1))) ∂(volC N) :=
    lintegral_const_mul _ hmeas
  have h4 : ∫⁻ x, (∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
        ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1))) ∂(volC N)
      = ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) ∂(volC N) :=
    lintegral_lintegral_sub_smul hHm y
  have hmain : ∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N)
      ≤ ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N) := by
    calc ∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N)
        ≤ ∫⁻ x, ENNReal.ofReal ‖y‖ ^ 2 * (∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
            ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1))) ∂(volC N) := h2
      _ = ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ x, (∫⁻ t, ENNReal.ofReal (‖fderiv ℝ f (x - t • y)‖ ^ 2)
            ∂(Measure.restrict volume (Set.Ioc (0:ℝ) 1))) ∂(volC N) := h3
      _ = ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N) := by
            rw [h4]
  -- ## Back to the Bochner integral
  have hIntR : Integrable (fun x : Conf N => ‖fderiv ℝ f x‖ ^ 2) (volC N) := integrable_fderiv_sq hf hcs
  have hfin : (∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N)) ≠ ⊤ := by
    have h := hIntR.hasFiniteIntegral
    simp only [MeasureTheory.HasFiniteIntegral] at h
    have hcongr : (∫⁻ x, ‖(fun x : Conf N => ‖fderiv ℝ f x‖ ^ 2) x‖ₑ ∂(volC N))
        = ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N) :=
      lintegral_congr (fun x => Real.enorm_eq_ofReal (sq_nonneg _))
    rw [hcongr] at h
    exact ne_of_lt h
  have hcontA : Continuous fun x : Conf N => (f x - f (x - y)) ^ 2 :=
    (continuous_pow 2).comp (hfc.sub (hfc.comp (by fun_prop : Continuous fun x : Conf N => x - y)))
  have hA : ∫ x, (f x - f (x - y)) ^ 2 ∂(volC N)
      = (∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg _))
      hcontA.aestronglyMeasurable
  have hC : ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(volC N)
      = (∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg _)) hIntR.aestronglyMeasurable
  have key : ENNReal.ofReal (∫ x, (f x - f (x - y)) ^ 2 ∂(volC N))
      ≤ ENNReal.ofReal (‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(volC N)) := by
    calc ENNReal.ofReal (∫ x, (f x - f (x - y)) ^ 2 ∂(volC N))
        = ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N)).toReal) := by
            rw [hA]
      _ ≤ ∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N) := ENNReal.ofReal_toReal_le
      _ ≤ ENNReal.ofReal ‖y‖ ^ 2 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N) := hmain
      _ = ENNReal.ofReal ‖y‖ ^ 2 * ENNReal.ofReal (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(volC N)) := by
            rw [hC, ENNReal.ofReal_toReal hfin]
      _ = ENNReal.ofReal (‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(volC N)) := by
            rw [← ENNReal.ofReal_pow hy0, ← ENNReal.ofReal_mul (sq_nonneg ‖y‖)]
  have hnn : 0 ≤ ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(volC N) :=
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => sq_nonneg _))
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp key

end Work.BoseSym.MollifyAux
