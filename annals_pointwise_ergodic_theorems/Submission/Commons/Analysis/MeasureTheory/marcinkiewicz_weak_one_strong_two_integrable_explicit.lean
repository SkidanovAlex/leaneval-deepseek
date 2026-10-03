import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable

/-!
# Marcinkiewicz interpolation, integrable form, explicit constant

This is the explicit-constant form of
`Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable`: the same
Marcinkiewicz interpolation theorem (weak type `(1,1)` with constant `A₀` and strong type
`(2,2)` with constant `A₁` on integrable functions, giving strong type `(p,p)` for
`1 < p < 2`), but with the constant
`(12 * A₀ * 2 ^ (p - 1) / (p - 1) + 16 * A₁ ^ 2 / (2 - p)) ^ (1 / p)`
made explicit.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal

namespace Commons.Analysis.MeasureTheory

theorem marcinkiewicz_weak_one_strong_two_integrable_explicit {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} (T : (α → E) → (β → E)) (hadd : ∀ f g : α → E, MeasureTheory.Integrable f μ → MeasureTheory.Integrable g μ → T (f + g) = T f + T g) {A0 A1 : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) (hweak : ∀ (f : α → E) (lam : ℝ), MeasureTheory.Integrable f μ → 0 < lam → ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * MeasureTheory.eLpNorm f 1 μ) (hstrong : ∀ f : α → E, MeasureTheory.Integrable f μ → MeasureTheory.eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f 2 μ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : ∀ f : α → E, MeasureTheory.Integrable f μ → MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal ((12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) ^ (1 / p)) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp1pos : 0 < p - 1 := by linarith
  have h2p : 0 < 2 - p := by linarith
  set K : ℝ := 12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < 12 * A0 * 2 ^ (p - 1) / (p - 1) := by positivity
    have h2 : 0 < 16 * A1 ^ 2 / (2 - p) := by positivity
    linarith
  intro f hint
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) μ = ∞
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hKpos _)).ne']
    exact le_top
  have hTm : AEStronglyMeasurable (T f) ν :=
    integrable_aestronglyMeasurable_T T hadd hweak hstrong hp1 hp2 hint hfin
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hTf : eLpNorm (T f) (ENNReal.ofReal p) ν = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hTm, htoReal]
  have hf : eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hint.aestronglyMeasurable, htoReal]
  rw [hTf, hf]
  have hmain : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤ ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    have hlayer := banach_lintegral_rpow_le_innerTail (ν := ν) (W := fun x => ‖T f x‖ₑ)
        (fun x => enorm_ne_top) hp0
    refine hlayer.trans ?_
    have hmaj : ∀ t : ℝ, 0 < t →
        innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
          ≤ ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
      intro t ht
      have h3 := high_pointwise_integrable (A0 := A0) (p := p) (T := T) (f := f) hA0 hp1 hint hweak ht
      have h4 := low_pointwise_innerTail_integrable (A1 := A1) (p := p) (T := T) (f := f) hA1 hp1 hint hstrong ht
      have hWVM : ∀ x, ‖T f x‖ₑ ≤
          ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ
            + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) := by
        intro x
        have hsum : Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f
            + Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f = f := banach_indicator_add_compl f
        have hkey : ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖ₑ
            + ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ := by
          conv_lhs => rw [← hsum, hadd (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f)
            (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f)
            (integrable_indicator_ofReal_lt_enorm hint t)
            (integrable_indicator_ofReal_lt_enorm_compl hint t)]
          exact enorm_add_le _ _
        calc ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖ₑ
              + ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ := hkey
          _ = ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ
              + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) := by
              rw [ofReal_norm]; ring
      have hdec := banach_innerTail_le (ν := ν) (W := fun x => ‖T f x‖ₑ)
          (V := fun x => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ)
          (w := fun x => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) hWVM ht
      calc innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
          ≤ (ν {a : β | t/2 < ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) a‖}
              + innerTail ν (fun a => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) a‖ₑ) (t/2))
              * ENNReal.ofReal (t^(p-1)) := mul_le_mul_left hdec _
        _ = ENNReal.ofReal (t^(p-1)) * ν {a : β | t/2 < ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) a‖}
              + ENNReal.ofReal (t^(p-1)) * innerTail ν (fun a => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) a‖ₑ) (t/2) := by
            ring
        _ ≤ _ := add_le_add h3 h4

    have hInt : ∫⁻ t in Set.Ioi (0:ℝ), innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
            + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hmaj t ht
    have hMA : Measurable (fun t : ℝ => ENNReal.ofReal (6 * A0 * t^(p-2)) *
        (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)) :=
      (measurable_ofReal_mul_rpow (c := 6 * A0) (q := p-2)).mul
        (measurable_lintegral_Ioi_half (innerTail_measurable μ _))
    have hML : Measurable (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
        (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) :=
      (measurable_ofReal_mul_rpow (c := 4 * A1^2) (q := p-3)).mul
        (measurable_lintegral_Ioc_sq (innerTail_measurable μ _))
    have hsplit := lintegral_add_left' (μ := volume.restrict (Set.Ioi (0:ℝ))) hMA.aemeasurable
        (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)))
    -- HIGH chain
    have hHigh : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) *
          (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
        ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := by
      have hT : Measurable (innerTail μ (fun x => ‖f x‖ₑ)) := innerTail_measurable μ _
      have hc : Measurable (fun t : ℝ => ENNReal.ofReal (6 * A0 * t^(p-2))) :=
        measurable_ofReal_mul_rpow (c := 6 * A0) (q := p-2)
      calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) *
            (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (6 * A0 * t^(p-2))) :=
            lintegral_Ioi_mul_Ioi_half_one hc hT
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * ∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (t^(p-2))) := by
            refine lintegral_congr fun s => ?_
            congr 1
            rw [show (∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (6 * A0 * t^(p-2)))
                = ∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (6 * A0) * ENNReal.ofReal (t^(p-2)) from
                lintegral_congr fun t =>
                  ENNReal.ofReal_mul (p := 6 * A0) (q := t^(p-2)) (by positivity),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2*s)^(p-1)/(p-1))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1
            congr 1
            rw [lintegral_Ioo_ofReal_rpow (X := 2*s) (q := p-2) (by linarith)
                (mul_nonneg (by norm_num) (le_of_lt (Set.mem_Ioi.1 hs))),
              show p - 2 + 1 = p - 1 by ring]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * (ENNReal.ofReal (2^(p-1)/(p-1)) * ENNReal.ofReal (s^(p-1)))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            rw [ofReal_rpow_scale (le_of_lt hs) hp1pos]
        _ = ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := by
            refine Eq.trans (lintegral_congr fun s => ?_)
              (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
            ring
        _ ≤ _ := le_rfl
    -- LOW chain
    have hLow : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))
        ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
      have hT : Measurable (innerTail μ (fun x => ‖f x‖ₑ)) := innerTail_measurable μ _
      have hTs : Measurable (fun s : ℝ => innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) :=
        hT.comp Real.continuous_sqrt.measurable
      have hc : Measurable (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3))) :=
        measurable_ofReal_mul_rpow (c := 4 * A1^2) (q := p-3)
      calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
            (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))
          = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (4 * A1^2 * t^(p-3))) :=
            lintegral_Ioi_mul_Ioc_sq_one hc hTs
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * ∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (t^(p-3))) := by
            refine lintegral_congr fun s => ?_
            congr 1
            rw [show (∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (4 * A1^2 * t^(p-3)))
                = ∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (t^(p-3)) from
                lintegral_congr fun t =>
                  ENNReal.ofReal_mul (p := 4 * A1^2) (q := t^(p-3)) (by positivity),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal ((Real.sqrt s)^(p-2)/(2-p))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1
            congr 1
            rw [lintegral_Ioi_ofReal_rpow (X := Real.sqrt s) (q := p-3) (by linarith) (Real.sqrt_pos.2 hs)]
            rw [show p - 3 + 1 = p - 2 by ring]
            congr 1
            rw [← div_neg, show (-(p-2)) = 2 - p by ring]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * (ENNReal.ofReal (1/(2-p)) * ENNReal.ofReal (s^((p-2)/2)))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            rw [ofReal_sqrt_rpow (le_of_lt hs) hp2]
        _ = ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
            refine Eq.trans (lintegral_congr fun s => ?_)
              (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
            ring
        _ ≤ _ := le_rfl
    -- the two tail integrals against `∫⁻ W ^ p`
    have hWT : ENNReal.ofReal p *
          (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))
        ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [show (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))
          = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^(p-1)) * innerTail μ (fun x => ‖f x‖ₑ) s from
          lintegral_congr fun s => mul_comm _ _]
      exact rpow_mul_innerTail_integral_le (μ := μ) (W := fun x => ‖f x‖ₑ) hp1
    have hST : ENNReal.ofReal p *
          (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
        ≤ 4 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [show (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
          = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^((p-2)/2)) * innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) from
          lintegral_congr fun s => mul_comm _ _]
      exact sqrt_innerTail_integral_le (μ := μ) (W := fun x => ‖f x‖ₑ) hp1
    -- constants
    have hCH : ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) * 2
        = ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * A0),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * A0 * (2^(p-1)/(p-1)))]
      congr 1
      ring
    have hCL : ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) * 4
        = ENNReal.ofReal (16 * A1^2/(2-p)) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2 * (1/(2-p)))]
      congr 1
      ring
    have hHighB : ENNReal.ofReal p *
          (ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))))
        ≤ ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      calc ENNReal.ofReal p *
            (ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))))
          = ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
              (ENNReal.ofReal p *
                (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))) := by
            ring
        _ ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) * (2 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
            mul_le_mul_right hWT _
        _ = ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
            rw [← hCH]; ring
    have hLowB : ENNReal.ofReal p *
          (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
        ≤ ENNReal.ofReal (16 * A1^2/(2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      calc ENNReal.ofReal p *
            (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
          = ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
              (ENNReal.ofReal p *
                (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))) := by
            ring
        _ ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) * (4 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
            mul_le_mul_right hST _
        _ = ENNReal.ofReal (16 * A1^2/(2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
            rw [← hCL]; ring
    calc ENNReal.ofReal p *
          (∫⁻ t in Set.Ioi (0:ℝ), innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1)))
        ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
            + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)))) :=
          mul_le_mul_right hInt _
      _ = ENNReal.ofReal p * ((∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s))
            + ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
          rw [hsplit]
      _ = ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s))
            + ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
          rw [mul_add]
      _ ≤ ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ
            + ENNReal.ofReal (16 * A1^2/(2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
          add_le_add ((mul_le_mul_right hHigh _).trans hHighB) ((mul_le_mul_right hLow _).trans hLowB)
      _ = ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), ← hK]
  calc (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p)
      ≤ (ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (ENNReal.ofReal K) ^ (1/p) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (K ^ (1/p)) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hKpos.le (by positivity)]

end Commons.Analysis.MeasureTheory
