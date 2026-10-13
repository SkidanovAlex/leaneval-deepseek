/-
Copyright: work module for the Elgindi finite-time singularity project.

# The rate estimate for the `I₄` boundary term (fallback proof)

If `F` is differentiable on `(0, π/2)` with `HasDerivAt F (deriv F)` there, and the weighted
square `(deriv F / cos θ)² · sin(2θ)^{-η}` is integrable on `(0, π/2)` (`η = 99/100`), then `F`
has a finite limit `L` at `π/2⁻` and

`(F θ - L)² ≤ 2^η (π/2-θ)^{3+η} ∫_θ^{π/2} (deriv F / cos)² sin(2θ)^{-η}`.

Route: Cauchy–Schwarz on `deriv F = (deriv F/cos θ)·cos θ` with the weight split
`sin(2θ)^{-η} = sin(2θ)^{-η/2} · sin(2θ)^{-η/2}` gives, for `θ < θ' < π/2`,

`|F θ' - F θ|² ≤ (∫_θ^{θ'} A) (∫_θ^{θ'} B)`,

where `A = (deriv F / cos)² sin(2θ)^{-η}` and `B = cos²θ sin(2θ)^η`; the elementary bound
`B ≤ 2^η (π/2-θ)^{2+η}` gives `∫_θ^{θ'} B ≤ 2^η (π/2-θ)^{3+η}`, and the limit `θ' → π/2` is
taken with `le_of_tendsto`.  The existence of `L` itself follows from the integrability of
`deriv F` on `(0, π/2)`, which in turn follows from the pointwise AM–GM bound
`|deriv F| ≤ (A + B)/2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.I4BV.Defs
import Submission.Work.FTS.EllipticEst.I4BV.exists_tendsto_nhdsLT_of_integrableOn_deriv
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I4BV

set_option autoImplicit false

theorem i4_rate_alt (F : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt F (deriv F x) x)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ L : ℝ,
      Filter.Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (F θ - L) ^ 2 ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
          * ∫ x in Set.Ioo θ (Real.pi / 2),
              (deriv F x / Real.cos x) ^ 2 * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by
  let I : Set ℝ := Set.Ioo 0 (Real.pi / 2)
  let A : ℝ → ℝ := fun θ => (deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
  let B : ℝ → ℝ := fun θ => (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)
  have hAnn : ∀ θ ∈ I, 0 ≤ A θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
      (by linarith [hθ'.2, Real.pi_pos])
    show 0 ≤ (deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have hBnn : ∀ θ ∈ I, 0 ≤ B θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
      (by linarith [hθ'.2, Real.pi_pos])
    show 0 ≤ (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have hAint : MeasureTheory.IntegrableOn A I := by
    show MeasureTheory.IntegrableOn (fun θ => (deriv F θ / Real.cos θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2))
    exact hint
  have hBcont : Continuous B := by
    show Continuous (fun θ => (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ))
    exact (Real.continuous_cos.pow 2).mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99 / 100)).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  have hBint : MeasureTheory.IntegrableOn B I := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hBcont.aestronglyMeasurable
      (2 ^ (99 / 100 : ℝ) * (Real.pi / 2) ^ (2 + 99 / 100 : ℝ)) ?_
    · show MeasureTheory.volume I < ⊤
      rw [show I = Set.Ioo 0 (Real.pi / 2) from rfl, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have h1 := cos_sq_mul_sin2_rpow_le hθ
      have h2 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have h3 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
      have h4 : (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) ≤ (Real.pi / 2) ^ (2 + 99 / 100 : ℝ) :=
        Real.rpow_le_rpow h2 h3 (by norm_num)
      have h5 : 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)
          ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2) ^ (2 + 99 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      have hBnn' : 0 ≤ (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _)
      show ‖B θ‖ ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2) ^ (2 + 99 / 100 : ℝ)
      rw [Real.norm_eq_abs]
      show |(Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)| ≤ _
      rw [abs_of_nonneg hBnn']
      linarith [h1, h5]
  have hAB : ∀ θ ∈ I, A θ * B θ = (deriv F θ) ^ 2 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩)
    have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1])
      (by linarith [hθ'.2, Real.pi_pos])
    show ((deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        * ((Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)) = (deriv F θ) ^ 2
    have hσ : (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ) = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    rw [show ((deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        * ((Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ))
        = ((deriv F θ) ^ 2 / (Real.cos θ) ^ 2 * (Real.cos θ) ^ 2)
          * ((Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
            * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)) by ring]
    rw [hσ, mul_one, div_mul_cancel₀ _ (pow_ne_zero 2 hc)]
  have hpt : ∀ θ ∈ I, |deriv F θ| ≤ (A θ + B θ) / 2 := by
    intro θ hθ
    have hAn : 0 ≤ A θ := hAnn θ hθ
    have hBn : 0 ≤ B θ := hBnn θ hθ
    have hAM : Real.sqrt (A θ * B θ) ≤ (A θ + B θ) / 2 := by
      have h1 : Real.sqrt (A θ * B θ) ^ 2 ≤ ((A θ + B θ) / 2) ^ 2 := by
        rw [Real.sq_sqrt (mul_nonneg hAn hBn)]
        nlinarith [sq_nonneg (A θ - B θ)]
      have h2 : 0 ≤ (A θ + B θ) / 2 := by linarith
      nlinarith [h1, Real.sqrt_nonneg (A θ * B θ), h2]
    have habs : |deriv F θ| = Real.sqrt (A θ * B θ) := by
      rw [hAB θ hθ, Real.sqrt_sq_eq_abs]
    rw [habs]
    exact hAM
  have hF'int : MeasureTheory.IntegrableOn (deriv F) I := by
    have hsum : MeasureTheory.IntegrableOn (fun θ => (A θ + B θ) / 2) I :=
      (hAint.add hBint).div_const 2
    refine MeasureTheory.Integrable.mono' hsum (measurable_deriv F).aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact hpt θ hθ
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      Filter.Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) := by
    refine exists_tendsto_nhdsLT_of_integrableOn_deriv (f' := deriv F)
      (b := Real.pi / 2) (δ := Real.pi / 2) (by linarith [Real.pi_pos]) ?_ ?_
    · intro x hx
      rw [show Real.pi / 2 - Real.pi / 2 = 0 by ring] at hx
      exact hF x hx
    · show MeasureTheory.IntegrableOn (deriv F) (Set.Ioo (Real.pi / 2 - Real.pi / 2) (Real.pi / 2))
      rw [show Real.pi / 2 - Real.pi / 2 = 0 by ring]
      exact hF'int
  refine ⟨L, hL, ?_⟩
  intro θ hθ
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
  have hu : 0 < Real.pi / 2 - θ := sub_pos.mpr hθI.2
  have hsub2 : Set.Ioo θ (Real.pi / 2) ⊆ I := fun x hx => ⟨lt_trans hθI.1 hx.1, hx.2⟩
  have hstep : ∀ θ' ∈ Set.Ioo θ (Real.pi / 2),
      (F θ - F θ') ^ 2 ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
        * ∫ x in Set.Ioo θ (Real.pi / 2), A x := by
    intro θ' hθ'
    have hsub : Set.Ioo θ θ' ⊆ I := fun x hx => ⟨lt_trans hθI.1 hx.1, lt_trans hx.2 hθ'.2⟩
    have hFT : ∫ x in Set.Ioo θ θ', deriv F x = F θ' - F θ := by
      have hm : ∫ x in Set.Ioo θ θ', deriv F x = ∫ x in Set.Ioc θ θ', deriv F x :=
        MeasureTheory.setIntegral_congr_set (μ := volume)
          (MeasureTheory.Ioo_ae_eq_Ioc (a := θ) (b := θ'))
      rw [hm, ← intervalIntegral.integral_of_le hθ'.1.le]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
      · rw [Set.uIcc_of_le hθ'.1.le] at hy
        exact hF y ⟨lt_of_lt_of_le hθI.1 hy.1, lt_of_le_of_lt hy.2 hθ'.2⟩
      · have hsub3 : Set.uIcc θ θ' ⊆ I := by
          rw [Set.uIcc_of_le hθ'.1.le]
          exact fun x hx => ⟨lt_of_lt_of_le hθI.1 hx.1, lt_of_le_of_lt hx.2 hθ'.2⟩
        exact (hF'int.mono_set hsub3).intervalIntegrable
    have hAii : MeasureTheory.IntegrableOn A (Set.Ioo θ θ') := hAint.mono_set hsub
    have hBii : MeasureTheory.IntegrableOn B (Set.Ioo θ θ') := hBint.mono_set hsub
    have hFii : MeasureTheory.IntegrableOn (deriv F) (Set.Ioo θ θ') := hF'int.mono_set hsub
    have hpt_s : ∀ x ∈ Set.Ioo θ θ', |deriv F x| ≤ Real.sqrt (A x) * Real.sqrt (B x) := by
      intro x hx
      have hxI : x ∈ I := hsub hx
      have h1 : |deriv F x| = Real.sqrt (A x * B x) := by
        rw [hAB x hxI, Real.sqrt_sq_eq_abs]
      rw [h1, Real.sqrt_mul (hAnn x hxI) (B x)]
    have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt hAii hBii hFii
      (fun x hx => hAnn x (hsub hx)) (fun x hx => hBnn x (hsub hx)) hpt_s
    have hAnnInt : 0 ≤ ∫ x in Set.Ioo θ θ', A x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun x hx => hAnn x (hsub hx))
    have hBnnInt : 0 ≤ ∫ x in Set.Ioo θ θ', B x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun x hx => hBnn x (hsub hx))
    have hAnnInt2 : 0 ≤ ∫ x in Set.Ioo θ (Real.pi / 2), A x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun x hx => hAnn x (hsub2 hx))
    have hsq : (F θ - F θ') ^ 2 ≤ (∫ x in Set.Ioo θ θ', A x) * (∫ x in Set.Ioo θ θ', B x) := by
      have heq : (F θ - F θ') ^ 2 = |∫ x in Set.Ioo θ θ', deriv F x| ^ 2 := by
        rw [hFT, sq_abs]; ring
      rw [heq]
      calc |∫ x in Set.Ioo θ θ', deriv F x| ^ 2
          ≤ (Real.sqrt (∫ x in Set.Ioo θ θ', A x) * Real.sqrt (∫ x in Set.Ioo θ θ', B x)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hcs 2
        _ = (∫ x in Set.Ioo θ θ', A x) * (∫ x in Set.Ioo θ θ', B x) := by
            rw [mul_pow, Real.sq_sqrt hAnnInt, Real.sq_sqrt hBnnInt]
    have hAle : ∫ x in Set.Ioo θ θ', A x ≤ ∫ x in Set.Ioo θ (Real.pi / 2), A x :=
      MeasureTheory.setIntegral_mono_set (hAint.mono_set hsub2)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => hAnn x (hsub2 hx)))
        (Filter.Eventually.of_forall (fun x hx => ⟨hx.1, lt_trans hx.2 hθ'.2⟩))
    have hBle : ∫ x in Set.Ioo θ θ', B x
        ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ) := by
      have hconst_int : MeasureTheory.IntegrableOn
          (fun _ : ℝ => 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ))
          (Set.Ioo θ θ') :=
        MeasureTheory.integrableOn_const
          (C := 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ))
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      have h1 : ∫ x in Set.Ioo θ θ', B x ≤ ∫ x in Set.Ioo θ θ',
          (fun _ : ℝ => 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)) x := by
        refine MeasureTheory.setIntegral_mono_on hBii hconst_int measurableSet_Ioo (fun x hx => ?_)
        have hxI : x ∈ I := hsub hx
        have hb1 := cos_sq_mul_sin2_rpow_le hxI
        have hb2 : Real.pi / 2 - x ≤ Real.pi / 2 - θ := by linarith [hx.1]
        have hb3 : 0 ≤ Real.pi / 2 - x := by linarith [hx.2, hθ'.2]
        have hb4 : (Real.pi / 2 - x) ^ (2 + 99 / 100 : ℝ)
            ≤ (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) :=
          Real.rpow_le_rpow hb3 hb2 (by norm_num)
        have hb5 : 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - x) ^ (2 + 99 / 100 : ℝ)
            ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hb4 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (99 / 100 : ℝ))
        show (Real.cos x) ^ 2 * (Real.sin (2 * x)) ^ (99 / 100 : ℝ)
          ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)
        exact le_trans hb1 hb5
      have h2 : ∫ x in Set.Ioo θ θ',
            (fun _ : ℝ => 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)) x
          = 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ) := by
        rw [MeasureTheory.setIntegral_const, Measure.real_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith [hθ'.1]), smul_eq_mul]
        ring
      rw [h2] at h1
      exact h1
    have hkey : 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ)
        ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ) := by
      have h2' : (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (1 : ℝ)
          = (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ) := by
        rw [← Real.rpow_add hu]
        norm_num
      have h1' : (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ)
          ≤ (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left (by linarith [hθ'.2]) (Real.rpow_nonneg (le_of_lt hu) _)
      rw [h2'] at h1'
      have h3 := mul_le_mul_of_nonneg_left h1'
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (99 / 100 : ℝ))
      linarith [h3]
    calc (F θ - F θ') ^ 2
        ≤ (∫ x in Set.Ioo θ θ', A x) * (∫ x in Set.Ioo θ θ', B x) := hsq
      _ ≤ (∫ x in Set.Ioo θ (Real.pi / 2), A x)
            * (2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ)) :=
          mul_le_mul hAle hBle hBnnInt hAnnInt2
      _ ≤ (∫ x in Set.Ioo θ (Real.pi / 2), A x)
            * (2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey hAnnInt2
      _ = 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
            * ∫ x in Set.Ioo θ (Real.pi / 2), A x := by ring
  have hmem : Set.Ioo θ (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (a := θ) (by linarith [hθI.2])]
    exact self_mem_nhdsWithin
  have htend : Filter.Tendsto (fun θ' => (F θ - F θ') ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((F θ - L) ^ 2)) := by
    simpa using ((tendsto_const_nhds.sub hL).pow 2)
  refine le_of_tendsto htend ?_
  filter_upwards [hmem] with θ' hθ'
  exact hstep θ' hθ'

end Work.FTS.EllipticEst.I4BV
