import Mathlib
import Submission.Work.Koebe.gwDefs
import Submission.Work.Koebe.cauchyTransform_ball
import Submission.Work.MRMT.Cauchy.inner_integral_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The degree (area) formula for a curve in the `1/z + H` normalisation

Let `F z = 1/z + H z` be injective on the punctured unit disc, with `H` holomorphic on the disc,
let `0 < r < 1` and let `Λ` bound `‖F‖` on the circle `|z| = r`.  Then the *signed area* of the
curve `θ ↦ F (r e^{iθ})`,

  `sArea F r = (2i)⁻¹ ∮_{|z|=r} conj (F z) · F'(z) dz`,

equals the integral, over the disc `|w| < Λ`, of the winding number `winding F r w` of that curve
around `w`.  This is the classical "area = integral of the index" formula (the degree formula).

The proof is the standard one: the Cauchy-kernel identity
`∫_{|w|<Λ} (ζ - w)⁻¹ dw = π · conj ζ` (valid for `‖ζ‖ < Λ`, proved in
`Submission/Work/Koebe/cauchyTransform_ball.lean`), Fubini's theorem, and the elementary
observation that this identity converts the inner `w`-integral of the winding integrand into
`π · conj (F (r e^{iθ}))`.

## Main results

* `Work.Koebe.circleIntegral_eq_interval`     : the circle integral as an interval integral;
* `Work.Koebe.lintegral_cauchy_inv_ball`      : the uniform `∫⁻` bound for the Cauchy kernel;
* `Work.Koebe.integrable_uncurry_winding`     : integrability of the uncurried winding integrand
  (this is the hypothesis needed to apply Fubini);
* `Work.Koebe.sArea_eq_integral_winding`      : the degree formula in analytic form;
* `Work.Koebe.degreeFormula`                  : the target statement.
-/

namespace Work.Koebe

open MeasureTheory Complex Metric
open scoped ENNReal

set_option linter.unusedVariables false

theorem circleIntegral_eq_interval (f : ℂ → ℂ) (r : ℝ) :
    (∮ z in C(0, r), f z)
      = ∫ θ in (0:ℝ)..2 * Real.pi, (circleMap 0 r θ * Complex.I) * f (circleMap 0 r θ) := by
  rw [circleIntegral]
  exact intervalIntegral.integral_congr fun θ _ => by rw [deriv_circleMap, smul_eq_mul]

lemma lintegral_cauchy_inv_ball (Λ : ℝ) (hΛ : 0 ≤ Λ) (ζ : ℂ) :
    ∫⁻ w in Metric.ball (0:ℂ) Λ, ENNReal.ofReal ‖(ζ - w)⁻¹‖ ≤ ENNReal.ofReal (8 * Real.pi * Λ) := by
  rw [show (∫⁻ w in Metric.ball (0:ℂ) Λ, ENNReal.ofReal ‖(ζ - w)⁻¹‖)
      = ∫⁻ w in Metric.ball (0:ℂ) Λ, ENNReal.ofReal ‖ζ - w‖⁻¹ from by
    apply setLIntegral_congr_fun measurableSet_ball
    intro w _
    simp only [norm_inv]]
  exact Work.MRMT.Cauchy.inner_integral_bound _ Λ hΛ subset_rfl ζ

theorem integrable_uncurry_winding (F : ℂ → ℂ) (r Λ M : ℝ) (hr : 0 < r) (hΛ : 0 ≤ Λ)
    (hFc : Continuous fun θ : ℝ => F (circleMap 0 r θ))
    (hdFc : Continuous fun θ : ℝ => deriv F (circleMap 0 r θ))
    (hMb : ∀ θ : ℝ, ‖deriv F (circleMap 0 r θ)‖ ≤ M) :
    Integrable (fun p : ℝ × ℂ =>
        (circleMap 0 r p.1 * Complex.I) * deriv F (circleMap 0 r p.1) * (F (circleMap 0 r p.1) - p.2)⁻¹)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume.restrict (Metric.ball (0:ℂ) Λ))) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMb 0)
  have hm1 : Measurable fun p : ℝ × ℂ => circleMap 0 r p.1 * Complex.I :=
    ((continuous_circleMap 0 r).measurable.comp measurable_fst).mul measurable_const
  have hm2 : Measurable fun p : ℝ × ℂ => deriv F (circleMap 0 r p.1) :=
    hdFc.measurable.comp measurable_fst
  have hm3 : Measurable fun p : ℝ × ℂ => (F (circleMap 0 r p.1) - p.2)⁻¹ :=
    ((hFc.measurable.comp measurable_fst).sub measurable_snd).inv
  have hmG : AEStronglyMeasurable
      (fun p : ℝ × ℂ => (circleMap 0 r p.1 * Complex.I) * deriv F (circleMap 0 r p.1)
        * (F (circleMap 0 r p.1) - p.2)⁻¹)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume.restrict (Metric.ball (0:ℂ) Λ))) :=
    ((hm1.mul hm2).mul hm3).aestronglyMeasurable
  have hmeasB : AEMeasurable
      (fun p : ℝ × ℂ => ENNReal.ofReal (r * M) * ENNReal.ofReal ‖(F (circleMap 0 r p.1) - p.2)⁻¹‖)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume.restrict (Metric.ball (0:ℂ) Λ))) :=
    (measurable_const.mul (ENNReal.measurable_ofReal.comp hm3.norm)).aemeasurable
  refine ⟨hmG, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hpoint : ∀ p : ℝ × ℂ,
      ENNReal.ofReal ‖(circleMap 0 r p.1 * Complex.I) * deriv F (circleMap 0 r p.1)
          * (F (circleMap 0 r p.1) - p.2)⁻¹‖
        ≤ ENNReal.ofReal (r * M) * ENNReal.ofReal ‖(F (circleMap 0 r p.1) - p.2)⁻¹‖ := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr,
      ← ENNReal.ofReal_mul (mul_nonneg hr.le hM0)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (hMb p.1) hr.le
  have hK : ∀ θ : ℝ, (∫⁻ w, ENNReal.ofReal ‖(F (circleMap 0 r θ) - w)⁻¹‖
        ∂(volume.restrict (Metric.ball (0:ℂ) Λ))) ≤ ENNReal.ofReal (8 * Real.pi * Λ) :=
    fun θ => lintegral_cauchy_inv_ball Λ hΛ (F (circleMap 0 r θ))
  have hKm : ∀ θ : ℝ, Measurable fun w : ℂ => ENNReal.ofReal ‖(F (circleMap 0 r θ) - w)⁻¹‖ := by
    intro θ
    have h1 : Measurable fun w : ℂ => (F (circleMap 0 r θ) - w)⁻¹ := by
      refine Measurable.inv ?_
      refine Measurable.sub ?_ measurable_id
      exact measurable_const
    exact ENNReal.measurable_ofReal.comp h1.norm
  calc ∫⁻ p, ENNReal.ofReal ‖(circleMap 0 r p.1 * Complex.I) * deriv F (circleMap 0 r p.1)
          * (F (circleMap 0 r p.1) - p.2)⁻¹‖
        ∂((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume.restrict (Metric.ball (0:ℂ) Λ)))
      ≤ ∫⁻ p, ENNReal.ofReal (r * M) * ENNReal.ofReal ‖(F (circleMap 0 r p.1) - p.2)⁻¹‖
        ∂((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume.restrict (Metric.ball (0:ℂ) Λ))) :=
        lintegral_mono hpoint
    _ = ∫⁻ θ, ∫⁻ w, ENNReal.ofReal (r * M) * ENNReal.ofReal ‖(F (circleMap 0 r θ) - w)⁻¹‖
          ∂(volume.restrict (Metric.ball (0:ℂ) Λ)) ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
        rw [lintegral_prod (f := fun p : ℝ × ℂ =>
          ENNReal.ofReal (r * M) * ENNReal.ofReal ‖(F (circleMap 0 r p.1) - p.2)⁻¹‖) hmeasB]
    _ = ∫⁻ θ, ENNReal.ofReal (r * M) * (∫⁻ w, ENNReal.ofReal ‖(F (circleMap 0 r θ) - w)⁻¹‖
          ∂(volume.restrict (Metric.ball (0:ℂ) Λ))) ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
        refine lintegral_congr fun θ => ?_
        exact lintegral_const_mul _ (hKm θ)
    _ ≤ ∫⁻ θ, ENNReal.ofReal (r * M) * ENNReal.ofReal (8 * Real.pi * Λ)
          ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
        refine lintegral_mono fun θ => ?_
        exact mul_le_mul_of_nonneg_left (hK θ) zero_le
    _ = ENNReal.ofReal (r * M) * ENNReal.ofReal (8 * Real.pi * Λ) * ENNReal.ofReal (2 * Real.pi) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_uIoc, sub_zero,
          abs_of_pos (by positivity)]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top

theorem sArea_eq_integral_winding (F : ℂ → ℂ) (r Λ M : ℝ) (hr : 0 < r) (hΛ : 0 < Λ)
    (hFc : Continuous fun θ : ℝ => F (circleMap 0 r θ))
    (hdFc : Continuous fun θ : ℝ => deriv F (circleMap 0 r θ))
    (hMb : ∀ θ : ℝ, ‖deriv F (circleMap 0 r θ)‖ ≤ M)
    (hFΛ : ∀ θ : ℝ, ‖F (circleMap 0 r θ)‖ < Λ) :
    sArea F r = ∫ w in Metric.ball 0 Λ, winding F r w := by
  have hint := integrable_uncurry_winding F r Λ M hr hΛ.le hFc hdFc hMb
  have hpi : (2 * (Real.pi:ℂ) * Complex.I)⁻¹ * (Real.pi:ℂ) = (2 * Complex.I)⁻¹ := by
    have h1 : (2 * (Real.pi:ℂ) * Complex.I) = (2 * Complex.I) * (Real.pi:ℂ) := by ring
    have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    have hp0 : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [h1, mul_inv, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
  have hsA : sArea F r = (2 * Complex.I)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi,
      (circleMap 0 r θ * Complex.I) * ((starRingEnd ℂ (F (circleMap 0 r θ))) * deriv F (circleMap 0 r θ)) := by
    rw [sArea, circleIntegral_eq_interval]
  have hinner : ∀ θ : ℝ, (∫ w in Metric.ball (0:ℂ) Λ,
        (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹)
      = (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ)
        * ((Real.pi:ℂ) * (starRingEnd ℂ (F (circleMap 0 r θ)))) := by
    intro θ
    have h1 : (∫ w in Metric.ball (0:ℂ) Λ,
          (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹)
        = ((circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ))
          * (∫ w in Metric.ball (0:ℂ) Λ, (F (circleMap 0 r θ) - w)⁻¹) := by
      rw [show (∫ w in Metric.ball (0:ℂ) Λ,
            (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹)
          = ∫ w in Metric.ball (0:ℂ) Λ,
            ((circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ)) * (F (circleMap 0 r θ) - w)⁻¹ from
          setIntegral_congr_fun measurableSet_ball fun w _ => by ring]
      rw [MeasureTheory.integral_const_mul]
    rw [h1, cauchyTransform_ball Λ hΛ (F (circleMap 0 r θ)) (hFΛ θ)]
  have hkey : (∫ w in Metric.ball (0:ℂ) Λ, winding F r w)
      = (2 * Complex.I)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi,
          (circleMap 0 r θ * Complex.I) * ((starRingEnd ℂ (F (circleMap 0 r θ))) * deriv F (circleMap 0 r θ)) := by
    have hw1 : (∫ w in Metric.ball (0:ℂ) Λ, winding F r w)
        = (2 * (Real.pi:ℂ) * Complex.I)⁻¹ * ∫ w in Metric.ball (0:ℂ) Λ, ∮ z in C(0, r), deriv F z / (F z - w) := by
      rw [show (∫ w in Metric.ball (0:ℂ) Λ, winding F r w)
          = ∫ w in Metric.ball (0:ℂ) Λ,
              (2 * (Real.pi:ℂ) * Complex.I)⁻¹ * (∮ z in C(0, r), deriv F z / (F z - w)) from rfl,
        MeasureTheory.integral_const_mul]
    have hswap : (∫ w in Metric.ball (0:ℂ) Λ, ∮ z in C(0, r), deriv F z / (F z - w))
        = ∫ θ in (0:ℝ)..2 * Real.pi, ∫ w in Metric.ball (0:ℂ) Λ,
            (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹ := by
      have h1 : (∫ w in Metric.ball (0:ℂ) Λ, ∮ z in C(0, r), deriv F z / (F z - w))
          = ∫ w in Metric.ball (0:ℂ) Λ, ∫ θ in (0:ℝ)..2 * Real.pi,
              (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹ := by
        refine setIntegral_congr_fun measurableSet_ball fun w _ => ?_
        rw [circleIntegral_eq_interval]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        rw [div_eq_mul_inv]
        ring
      rw [h1]
      exact (MeasureTheory.intervalIntegral_integral_swap (f := fun θ w =>
        (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹) hint).symm
    have hstep : (∫ θ in (0:ℝ)..2 * Real.pi, ∫ w in Metric.ball (0:ℂ) Λ,
            (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ) * (F (circleMap 0 r θ) - w)⁻¹)
        = ∫ θ in (0:ℝ)..2 * Real.pi,
            (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ)
              * ((Real.pi:ℂ) * (starRingEnd ℂ (F (circleMap 0 r θ)))) :=
      intervalIntegral.integral_congr fun θ _ => hinner θ
    have hpull : (∫ θ in (0:ℝ)..2 * Real.pi,
            (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ)
              * ((Real.pi:ℂ) * (starRingEnd ℂ (F (circleMap 0 r θ)))))
        = (Real.pi:ℂ) * ∫ θ in (0:ℝ)..2 * Real.pi,
            (circleMap 0 r θ * Complex.I) * deriv F (circleMap 0 r θ)
              * (starRingEnd ℂ (F (circleMap 0 r θ))) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun θ _ => by ring
    rw [hw1, hswap, hstep, hpull, ← mul_assoc, hpi]
    congr 1
    exact intervalIntegral.integral_congr fun θ _ => by ring
  exact hsA.trans hkey.symm

theorem degreeFormula (F H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hF : Set.InjOn F (Metric.ball 0 1 \ {0}))
    (hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, F z = 1 / z + H z)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (Λ : ℝ) (hΛ : ∀ z, ‖z‖ = r → ‖F z‖ < Λ) :
    Work.Koebe.sArea F r = ∫ w in Metric.ball 0 Λ, Work.Koebe.winding F r w := by
  have hUopen : IsOpen (Metric.ball (0:ℂ) 1 \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hFd : DifferentiableOn ℂ F (Metric.ball (0:ℂ) 1 \ {0}) := by
    refine ((differentiableOn_id.inv ?_).add (hH.mono ?_)).congr ?_
    · intro w hw; exact hw.2
    · intro w hw; exact hw.1
    · intro w hw
      have h := hexp w hw
      rw [one_div] at h
      exact h
  have hderivcont : ContinuousOn (deriv F) (Metric.ball (0:ℂ) 1 \ {0}) :=
    ((hFd.analyticOnNhd hUopen).contDiffOn hUopen.uniqueDiffOn).continuousOn_deriv_of_isOpen hUopen le_rfl
  have hsphere_sub : Metric.sphere (0:ℂ) r ⊆ Metric.ball (0:ℂ) 1 \ {0} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hz']; exact hr1
    · simp only [Set.mem_singleton_iff]; intro h; rw [h] at hz'; simp at hz'; linarith
  have hFc : Continuous fun θ : ℝ => F (circleMap 0 r θ) :=
    (hFd.continuousOn.mono hsphere_sub).comp_continuous (continuous_circleMap 0 r)
      (fun θ => circleMap_mem_sphere 0 hr.le θ)
  have hdFc : Continuous fun θ : ℝ => deriv F (circleMap 0 r θ) :=
    (hderivcont.mono hsphere_sub).comp_continuous (continuous_circleMap 0 r)
      (fun θ => circleMap_mem_sphere 0 hr.le θ)
  obtain ⟨M, hM⟩ := (isCompact_sphere (0:ℂ) r).exists_bound_of_continuousOn
    (hderivcont.mono hsphere_sub)
  have hMb : ∀ θ : ℝ, ‖deriv F (circleMap 0 r θ)‖ ≤ M :=
    fun θ => hM _ (circleMap_mem_sphere 0 hr.le θ)
  have hFΛ : ∀ θ : ℝ, ‖F (circleMap 0 r θ)‖ < Λ :=
    fun θ => hΛ _ (by rw [norm_circleMap_zero, abs_of_pos hr])
  have hΛpos : 0 < Λ := lt_of_le_of_lt (norm_nonneg _) (hFΛ 0)
  exact sArea_eq_integral_winding F r Λ M hr hΛpos hFc hdFc hMb hFΛ

end Work.Koebe
