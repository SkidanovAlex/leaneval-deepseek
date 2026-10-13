import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one
import Submission.Work.FTS.PhiStar.Honesty.rgG1_pt_bound
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioi
import Submission.Work.FTS.PhiStar.Honesty.ofReal_integral_rpow_mul_sq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 1600000

/-- **`lintegral` bound for the far-field square of the decaying Green branch.**

The pointwise bound `rgG1_pt_bound`, the Cauchy–Schwarz/Tonelli computation
`∫_1^∞ z^{-q} ∫_1^z (c t)² t^{q-1} dt dz = (1/(q-1)) ∫_1^∞ (c t)² dt` (Taubinian swap
`lintegral_tail_swap_Ioi_one`, evaluation `lintegral_ofReal_rpow_Ioi`), and the `ofReal`
identification `ofReal_integral_rpow_mul_sq_eq_lintegral` combine to give the stated bound. -/
theorem rgG1_lintegral_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
      ≤ ENNReal.ofReal (2 * (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t) ^ 2
            / (2 * Work.FTS.EllExist.rgQ α m - 1)
          + 2 * (1 / (Work.FTS.EllExist.rgQ α m - 1))
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
  have hqm1 : 0 < Work.FTS.EllExist.rgQ α m - 1 := by
    have := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have h2qm1 : 0 < 2 * Work.FTS.EllExist.rgQ α m - 1 := by
    have := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  set A0 : ℝ := ∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t with hA0
  set KK : ℝ → ℝ := fun z => ∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)
    with hKK
  have hpt : ∀ z : ℝ, 1 < z →
      (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))
          + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
    intro z hz
    simpa [hA0, hKK] using rgG1_pt_bound hα hα4 hm hc hnear hfar z hz
  have hKKnn : ∀ z : ℝ, 1 ≤ z → 0 ≤ KK z := by
    intro z hz
    simp only [hKK]
    exact intervalIntegral.integral_nonneg hz
      (fun t ht => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one ht.1) _))
  -- ### measurability of the two ENNReal integrands
  have hP : AEMeasurable (fun u : ℝ => ENNReal.ofReal ((c u) ^ 2 * u ^ (Work.FTS.EllExist.rgQ α m - 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have h1 : AEMeasurable c (volume.restrict (Set.Ioi (1 : ℝ))) := hc.restrict
    have h2 : AEMeasurable (fun u : ℝ => u ^ (Work.FTS.EllExist.rgQ α m - 1)) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (measurable_id.pow_const (Work.FTS.EllExist.rgQ α m - 1)).aemeasurable
    have h4 : AEMeasurable (fun u : ℝ => (c u) ^ 2 * u ^ (Work.FTS.EllExist.rgQ α m - 1))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (h1.pow_const 2).mul h2
    exact h4.ennreal_ofReal
  have hQ : AEMeasurable (fun u : ℝ => ENNReal.ofReal (u ^ (-(Work.FTS.EllExist.rgQ α m))))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((measurable_id.pow_const (-(Work.FTS.EllExist.rgQ α m))).aemeasurable).ennreal_ofReal
  -- ### the `ENNReal`-level pointwise bound
  have hptE : ∀ z : ℝ, 1 < z →
      ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2)
        ≤ ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))
          + ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))) := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have h1nn : 0 ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A0)) (Real.rpow_nonneg hz0.le _)
    have h2nn : 0 ≤ 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hz0.le _))
        (hKKnn z (le_of_lt hz))
    have h := ENNReal.ofReal_le_ofReal (hpt z hz)
    rw [ENNReal.ofReal_add h1nn h2nn] at h
    have h2nn' : 0 ≤ 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hz0.le _)
    rw [ENNReal.ofReal_mul h2nn'] at h
    simp only [hKK] at h
    rw [ofReal_integral_rpow_mul_sq_eq_lintegral hα hα4 hm hc hfar z (le_of_lt hz)] at h
    exact h
  -- ### the evaluation of the first term
  have hA0part : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
      = ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by
    have hz2q : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
        = ENNReal.ofReal (1 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by
      have h := lintegral_ofReal_rpow_Ioi (p := -(2 * Work.FTS.EllExist.rgQ α m)) (z := 1) (by linarith) (by norm_num)
      rw [Real.one_rpow] at h
      have h2 : -(1 : ℝ) / (-(2 * Work.FTS.EllExist.rgQ α m) + 1) = 1 / (2 * Work.FTS.EllExist.rgQ α m - 1) := by
        rw [show -(2 * Work.FTS.EllExist.rgQ α m) + 1 = -(2 * Work.FTS.EllExist.rgQ α m - 1) from by ring, div_neg, neg_div, neg_neg]
      rwa [h2] at h
    calc (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
        = ∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (2 * A0 ^ 2) * ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          exact ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (2 * A0 ^ 2)
            * ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m))) :=
          lintegral_const_mul' (ENNReal.ofReal (2 * A0 ^ 2))
            (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))) ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 * A0 ^ 2) * ENNReal.ofReal (1 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by rw [hz2q]
      _ = ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- ### the evaluation of the second term
  have hKpart : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
        (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
      ≤ ENNReal.ofReal (2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
    have hinner : ∀ z ∈ Set.Ioi (1 : ℝ),
        (∫⁻ t in Set.Ioi z, ENNReal.ofReal (t ^ (-(Work.FTS.EllExist.rgQ α m))))
          = ENNReal.ofReal (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1)) := by
      intro z hz
      have hz0 : 0 < z := lt_trans zero_lt_one hz
      have h := lintegral_ofReal_rpow_Ioi (p := -(Work.FTS.EllExist.rgQ α m)) (z := z) (by linarith) hz0
      rwa [show -(z ^ (-(Work.FTS.EllExist.rgQ α m) + 1)) / (-(Work.FTS.EllExist.rgQ α m) + 1) = z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1) from by
            rw [show -(Work.FTS.EllExist.rgQ α m) + 1 = -(Work.FTS.EllExist.rgQ α m - 1) from by ring, div_neg, neg_div, neg_neg,
              show -(Work.FTS.EllExist.rgQ α m - 1) = 1 - Work.FTS.EllExist.rgQ α m from by ring]] at h
    have hswap := lintegral_tail_swap_Ioi_one
      (P := fun u : ℝ => ENNReal.ofReal ((c u) ^ 2 * u ^ (Work.FTS.EllExist.rgQ α m - 1)))
      (Q := fun u : ℝ => ENNReal.ofReal (u ^ (-(Work.FTS.EllExist.rgQ α m)))) hP hQ
      (fun u => ENNReal.ofReal_ne_top) (fun u => ENNReal.ofReal_ne_top)
    have hchain : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
          (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
        = ENNReal.ofReal ((1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in (Set.Ioi (1 : ℝ) ∩ Set.Iio z), ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))) from by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
        have hsub : Set.Ioo (1 : ℝ) z = Set.Ioi (1 : ℝ) ∩ Set.Iio z := by
          ext x
          exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
        rw [hsub]]
      rw [← hswap]
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1)) *
            (∫⁻ t in Set.Ioi z, ENNReal.ofReal (t ^ (-(Work.FTS.EllExist.rgQ α m)))))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1)) *
              ENNReal.ofReal (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1)) from by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
            rw [hinner z hz]]
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1)) *
            ENNReal.ofReal (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1)))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2) * ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)) from by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
            have hz0 : 0 < z := lt_trans zero_lt_one hz
            rw [← ENNReal.ofReal_mul
                (mul_nonneg (sq_nonneg (c z)) (Real.rpow_nonneg hz0.le _)),
              ← ENNReal.ofReal_mul (sq_nonneg (c z))]
            congr 1
            have hnum : z ^ (Work.FTS.EllExist.rgQ α m - 1) * z ^ (1 - Work.FTS.EllExist.rgQ α m) = 1 := by
              rw [← Real.rpow_add hz0, show Work.FTS.EllExist.rgQ α m - 1 + (1 - Work.FTS.EllExist.rgQ α m) = 0 from by ring, Real.rpow_zero]
            calc (c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1) * (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1))
                = (c z) ^ 2 * (z ^ (Work.FTS.EllExist.rgQ α m - 1) * z ^ (1 - Work.FTS.EllExist.rgQ α m)) / (Work.FTS.EllExist.rgQ α m - 1) := by ring
              _ = (c z) ^ 2 * 1 / (Work.FTS.EllExist.rgQ α m - 1) := by rw [hnum]
              _ = (c z) ^ 2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) := by ring]
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2) * ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)) * ENNReal.ofReal ((c z) ^ 2) from by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => mul_comm _ _)]
      rw [lintegral_const_mul' (ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)))
        (fun z : ℝ => ENNReal.ofReal ((c z) ^ 2)) ENNReal.ofReal_ne_top]
      rw [← ofReal_integral_eq_lintegral_ofReal hfar (ae_of_all _ (fun t => sq_nonneg _))]
      rw [← ENNReal.ofReal_mul (le_of_lt (div_pos one_pos hqm1))]
    calc (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
          (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
        = ∫⁻ z in Set.Ioi (1 : ℝ), (ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m)))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 : ℝ) *
            (ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          ring
      _ = ENNReal.ofReal (2 : ℝ) * (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 : ℝ) *
            ENNReal.ofReal ((1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
          rw [hchain]
      _ ≤ ENNReal.ofReal (2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
          exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  -- ### assemble
  have hPnn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
  have hbound : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
      ≤ ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1)
          + 2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
    have hm1 : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
        ≤ ∫⁻ z in Set.Ioi (1 : ℝ), (ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))
            + ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact hptE z hz
    have hm2 : (∫⁻ z in Set.Ioi (1 : ℝ), (ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))
            + ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))))
        = (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
          + (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) :=
      lintegral_add_left'
        ((measurable_const.mul (measurable_id.pow_const (-(2 * Work.FTS.EllExist.rgQ α m)))).aemeasurable.ennreal_ofReal) _
    rw [hm2, hA0part] at hm1
    have hAB : ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1))
          + (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
        ≤ ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1))
          + ENNReal.ofReal (2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
      add_le_add (le_refl _) hKpart
    refine hm1.trans (hAB.trans ?_)
    exact (ENNReal.ofReal_add
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg A0)) (le_of_lt h2qm1))
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hPnn)).symm.le
  simpa [hA0] using hbound

end Work.FTS.PhiStar.Honesty
