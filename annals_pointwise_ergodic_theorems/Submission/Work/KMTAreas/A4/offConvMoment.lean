import Mathlib
import Submission.Work.KMTAreas.A4.diffEnormLe
import Submission.Work.KMTAreas.A4.convPointwiseEnormLe
import Submission.Work.KMTAreas.A4.offConvMomentConversion

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- **Moment (first-order) estimate for the smoothing by a normalised Schwartz kernel.**  If
`∫ v = 1` then the `L¹` distance from `h` to its convolution with `v` is bounded by the first
moment of `v` times the `L¹` norm of the derivative of `h`.  The proof is the standard one:

* per point, `h x - (h ⋆ v) x = ∫ y, (h x - h (x - y)) * v y`, so
  `‖h x - (h ⋆ v) x‖ₑ ≤ ∫⁻ y, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ` (`convPointwiseEnormLe`);
* integrating in `x`, Tonelli's theorem and translation invariance of Lebesgue measure give
  `∫⁻ x, ‖h x - (h ⋆ v) x‖ₑ ≤ (∫⁻ y, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x, ‖deriv h x‖ₑ`, the inner bound
  `∫⁻ x, ‖h x - h (x - y)‖ₑ ≤ ‖y‖ₑ * ∫⁻ x, ‖deriv h x‖ₑ` being `diffEnormLe`;
* converting back from `ℝ≥0∞` to `ℝ` (`offConvMomentConversion`) yields the claim. -/
theorem offConvMoment (h v : SchwartzMap ℝ ℂ) (hv1 : ∫ y : ℝ, v y = 1) :
    ∫ x : ℝ, ‖h x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x‖
      ≤ (∫ y : ℝ, |y| * ‖v y‖) * ∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ := by
  set F : ℝ → ℂ := fun x => h x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x with hF
  have hFcont : Continuous F :=
    h.continuous.sub (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v).continuous
  -- Tonelli: swap the two lintegrals
  have hswap : ∫⁻ x : ℝ, ∫⁻ y : ℝ, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ
      = ∫⁻ y : ℝ, ∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ := by
    refine lintegral_lintegral_swap ?_
    rw [show (Function.uncurry fun x y : ℝ => ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ)
        = (fun p : ℝ × ℝ => ‖h p.1 - h (p.1 - p.2)‖ₑ * ‖v p.2‖ₑ) from rfl]
    have c1 : Continuous (fun p : ℝ × ℝ => h p.1 - h (p.1 - p.2)) :=
      (h.continuous.comp continuous_fst).sub (h.continuous.comp (continuous_fst.sub continuous_snd))
    have c2 : Continuous (fun p : ℝ × ℝ => v p.2) := v.continuous.comp continuous_snd
    exact (c1.enorm.aemeasurable).mul (c2.enorm.aemeasurable)
  -- pull the `y`-constant out of the inner lintegral
  have hpull : ∫⁻ y : ℝ, (∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ)
      = ∫⁻ y : ℝ, ‖v y‖ₑ * (∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ) := by
    refine lintegral_congr (fun y => ?_)
    rw [lintegral_mul_const (‖v y‖ₑ) (f := fun x : ℝ => ‖h x - h (x - y)‖ₑ) (by
      exact ((h.continuous.sub (h.continuous.comp (continuous_id.sub continuous_const))).enorm).measurable)]
    rw [mul_comm]
  -- apply the translation-difference bound `diffEnormLe` for each `y`
  have hmono : ∫⁻ y : ℝ, ‖v y‖ₑ * (∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ)
      ≤ ∫⁻ y : ℝ, ‖v y‖ₑ * (‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ) :=
    lintegral_mono (fun y => mul_le_mul_right (diffEnormLe h y) (‖v y‖ₑ))
  -- collect the constants
  have hpull2 : ∫⁻ y : ℝ, ‖v y‖ₑ * (‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ)
      = (∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ := by
    rw [show (fun y : ℝ => ‖v y‖ₑ * (‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ))
        = (fun y : ℝ => (‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ) from
      funext (fun y => by ac_rfl)]
    rw [lintegral_mul_const _ (f := fun y : ℝ => ‖y‖ₑ * ‖v y‖ₑ)
      (Measurable.mul continuous_enorm.measurable v.continuous.enorm.measurable)]
  have hchain : ∫⁻ x : ℝ, ‖F x‖ₑ
      ≤ (∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ :=
    calc ∫⁻ x : ℝ, ‖F x‖ₑ
        ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ :=
          lintegral_mono (fun x => convPointwiseEnormLe h v hv1 x)
      _ = ∫⁻ y : ℝ, ∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ := hswap
      _ = ∫⁻ y : ℝ, ‖v y‖ₑ * (∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ) := hpull
      _ ≤ ∫⁻ y : ℝ, ‖v y‖ₑ * (‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ) := hmono
      _ = (∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ := hpull2
  -- finiteness of the right-hand side, via the `ofReal` conversion
  have hfin : (∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ ≠ ⊤ := by
    rw [← offConvMomentConversion h v]
    exact ENNReal.ofReal_ne_top
  calc ∫ x : ℝ, ‖h x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x‖
      = (∫⁻ x : ℝ, ‖F x‖ₑ).toReal := integral_norm_eq_lintegral_enorm hFcont.aestronglyMeasurable
    _ ≤ ((∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ).toReal :=
        ENNReal.toReal_mono hfin hchain
    _ = (ENNReal.ofReal
          ((∫ y : ℝ, |y| * ‖v y‖) * ∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖)).toReal := by
        rw [offConvMomentConversion h v]
    _ = (∫ y : ℝ, |y| * ‖v y‖) * ∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ :=
        ENNReal.toReal_ofReal (mul_nonneg (integral_nonneg (fun y => by positivity))
          (integral_nonneg (fun x => norm_nonneg _)))

end Work.KMTAreas.A4
