import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo
import Submission.Work.FTS.EllExist.Honesty.psi_cs
import Submission.Work.FTS.EllExist.Honesty.psi_inner_wt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Measurability of the tail integral -/

/-- The tail integral `z ↦ ∫ t in (z,∞), f t` is a.e. strongly measurable on `(0,∞)`
whenever `f` is. -/
lemma aestronglyMeasurable_tailIntegral {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0))) :
    AEStronglyMeasurable (fun z => ∫ t in Set.Ioi z, f t) (volume.restrict (Set.Ioi 0)) := by
  set μ : Measure ℝ := volume.restrict (Set.Ioi 0) with hμ
  have hbase : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (μ.prod μ) := hf.comp_snd
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hind : AEStronglyMeasurable
      (Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p : ℝ × ℝ => f p.2)) (μ.prod μ) :=
    hbase.indicator hset
  have hmeas : AEStronglyMeasurable
      (fun z => ∫ t, Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p : ℝ × ℝ => f p.2) (z, t) ∂μ) μ :=
    hind.integral_prod_right'
  refine hmeas.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hpt : (fun t : ℝ => Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p : ℝ × ℝ => f p.2) (z, t))
      = Set.indicator (Set.Ioi z) f := by
    funext t
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  rw [hpt, hμ]
  rw [integral_indicator measurableSet_Ioi]
  have hsub : Set.Ioi z ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_trans (show (0:ℝ) < z from hz) ht
  rw [Measure.restrict_restrict_of_subset hsub]

/-- Tonelli for the tail kernel. -/
lemma lintegral_tail_swap {P Q : ℝ → ℝ≥0∞}
    (hP : AEMeasurable P (volume.restrict (Set.Ioi 0)))
    (hQ : AEMeasurable Q (volume.restrict (Set.Ioi 0)))
    (hPtop : ∀ z, P z ≠ ⊤) (hQtop : ∀ t, Q t ≠ ⊤) :
    ∫⁻ z in Set.Ioi 0, P z * (∫⁻ t in Set.Ioi z, Q t)
      = ∫⁻ t in Set.Ioi 0, Q t * (∫⁻ z in (Set.Ioi 0 ∩ Set.Iio t), P z) := by
  have hmem : ∀ z ∈ Set.Ioi (0:ℝ), Set.Ioi z ⊆ Set.Ioi (0:ℝ) :=
    fun z hz => Set.Ioi_subset_Ioi (le_of_lt hz)
  have h3 : AEMeasurable (fun p : ℝ × ℝ => P p.1 * Q p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    (hP.comp_fst).mul (hQ.comp_snd)
  have h4 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hAEM : AEMeasurable (Function.uncurry (fun z t : ℝ => if z < t then P z * Q t else 0))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    rw [show (Function.uncurry (fun z t : ℝ => if z < t then P z * Q t else 0))
        = Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p : ℝ × ℝ => P p.1 * Q p.2) from by
      funext p
      obtain ⟨a, b⟩ := p
      by_cases h : a < b <;>
        simp [h, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_setOf_eq]]
    exact h3.indicator h4
  have hL : ∫⁻ z in Set.Ioi 0, P z * (∫⁻ t in Set.Ioi z, Q t)
      = ∫⁻ z, ∫⁻ t, (if z < t then P z * Q t else 0)
          ∂(volume.restrict (Set.Ioi 0)) ∂(volume.restrict (Set.Ioi 0)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [← Measure.restrict_restrict_of_subset (hmem z hz)]
    rw [← lintegral_indicator measurableSet_Ioi (f := Q)]
    rw [← lintegral_const_mul' (P z) _ (hPtop z)]
    refine lintegral_congr fun t => ?_
    by_cases h : z < t <;> simp [h, Set.indicator_of_mem, Set.indicator_of_notMem,
      Set.mem_Ioi, Set.mem_Iio]
  rw [hL, lintegral_lintegral_swap hAEM]
  have hR : ∫⁻ t, ∫⁻ z, (if z < t then P z * Q t else 0)
      ∂(volume.restrict (Set.Ioi 0)) ∂(volume.restrict (Set.Ioi 0))
      = ∫⁻ t in Set.Ioi 0, Q t * (∫⁻ z in (Set.Ioi 0 ∩ Set.Iio t), P z) := by
    refine lintegral_congr fun t => ?_
    rw [show (fun z : ℝ => (if z < t then P z * Q t else 0))
        = (fun z : ℝ => (if z < t then P z else 0) * Q t) from by
      funext z
      by_cases h : z < t <;> simp [h]]
    rw [lintegral_mul_const' (Q t) _ (hQtop t)]
    have key : (∫⁻ z, (if z < t then P z else 0) ∂(volume.restrict (Set.Ioi 0)))
        = ∫⁻ z in (Set.Ioi 0 ∩ Set.Iio t), P z := by
      rw [show (fun z : ℝ => (if z < t then P z else 0)) = (Set.Iio t).indicator P from by
        funext z
        by_cases h : z < t <;>
          simp [h, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_Iio]]
      rw [lintegral_indicator measurableSet_Iio]
      rw [Measure.restrict_restrict measurableSet_Iio]
      rw [Set.inter_comm (Set.Iio t) (Set.Ioi (0:ℝ))]
    rw [key, mul_comm]
  exact hR

/-- `w z ^ 2 ≥ 1` for `z > 0`. -/
lemma w_sq_ge_one {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz0 : (0:ℝ) < (z ^ 2) ^ 2 := by positivity
  have hle : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
  have h2 : (z ^ 2) ^ 2 ≤ ((1 + z) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
  simp only [Work.Spaces.w]
  rw [div_pow, one_le_div hz0]
  exact h2

/-- `ofReal` of a set integral is at most the set lintegral of `ofReal`. -/
lemma ofReal_setIntegral_le_setLIntegral {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hnn : 0 ≤ᵐ[volume.restrict s] f) :
    ENNReal.ofReal (∫ t in s, f t) ≤ ∫⁻ t in s, ENNReal.ofReal (f t) := by
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hf]
  exact ENNReal.ofReal_toReal_le

/-- `w` is continuous on `(0,∞)`. -/
lemma continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuous_const.continuousOn.add continuous_id.continuousOn).pow 2)
    (continuous_id.continuousOn.pow 2) (fun x hx => ?_)
  exact pow_ne_zero 2 (ne_of_gt hx)

/-- The elementary pointwise consequence of Cauchy–Schwarz driving the envelope estimate. -/
lemma psi_pointwise {p : ℝ} (hp : 0 < p) {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hcs : (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
        ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) :
    (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (1 / p) * ((z ^ p * (Work.Spaces.w z) ^ 2)
          * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) := by
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz p
  have hzpp : z ^ p * z ^ (-p) = 1 := by
    rw [← Real.rpow_add hz, show p + (-p) = 0 by ring, Real.rpow_zero]
  have hsq : (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2
      = z ^ p * (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2) := by
    rw [mul_pow]
    ring
  have hstep : z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (1 / p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    have h := mul_le_mul_of_nonneg_left hcs (le_of_lt hzp)
    calc z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
        ≤ z ^ p * ((1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) := h
      _ = (1 / p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
          rw [show z ^ p * ((1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))
              = (z ^ p * z ^ (-p)) * ((1 / p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) by ring,
            hzpp]
          ring
  calc (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2
      = z ^ p * (Work.Spaces.w z) ^ 2
          * (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2) := by
        rw [hsq]; ring
    _ ≤ z ^ p * (Work.Spaces.w z) ^ 2
          * ((1 / p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (1 / p) * ((z ^ p * (Work.Spaces.w z) ^ 2)
          * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) := by ring

theorem radGreen_psiEnvelope {p : ℝ} (hp : 6 ≤ p) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h1 : MeasureTheory.IntegrableOn (fun z => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
        (fun z => (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (1 / (p * (p - 3))) * (∫ z in Work.Spaces.Iz, (c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hp4 : (4:ℝ) ≤ p := by linarith
  have hp3 : (0:ℝ) < p - 3 := by linarith
  -- (A) `c ^ 2` is integrable on `(z,∞)` for `z > 0`
  have hc2int : ∀ z ∈ Set.Ioi (0:ℝ), MeasureTheory.IntegrableOn (fun t => (c t) ^ 2) (Set.Ioi z) := by
    intro z hz
    have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
      intro t ht
      show (0:ℝ) ≤ t
      exact le_of_lt (lt_trans hz ht)
    have hbase : MeasureTheory.IntegrableOn (fun t => (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (Set.Ioi z) := h1.mono_set hsub
    refine hbase.mono' ?_ ?_
    · exact ((hc.mono (Set.Ioi_subset_Ioi (le_of_lt hz))).aestronglyMeasurable
        measurableSet_Ioi).pow 2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz ht
      have hcsq : 0 ≤ (c t) ^ 2 := sq_nonneg _
      have hwt : 1 ≤ (Work.Spaces.w t) ^ 2 := w_sq_ge_one ht0
      have hnum : 0 ≤ (c t) ^ 2 * (Work.Spaces.w t) ^ 2 := mul_nonneg hcsq (by positivity)
      rw [Real.norm_of_nonneg hcsq]
      exact le_mul_of_one_le_right hcsq hwt
  -- continuity of the pieces
  have hcontF : ContinuousOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioi 0) :=
    hc.mul ((continuous_id.continuousOn).rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
  have hcontP : ContinuousOn (fun z : ℝ => z ^ p * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    ((continuous_id.continuousOn).rpow_const (fun x hx => Or.inr (le_of_lt hp0))).mul
      (continuousOn_w.pow 2)
  have hcontQ : ContinuousOn (fun t : ℝ => (c t) ^ 2 * t ^ (-p - 1)) (Set.Ioi 0) :=
    (hc.pow 2).mul ((continuous_id.continuousOn).rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
  -- (B) the pointwise ENNReal bound
  have hpt : ∀ z ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
            * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
    intro z hz
    have hreal := psi_pointwise hp0 hz (psi_cs hp0 hc hz (hc2int z hz))
    have hzWnn : 0 ≤ z ^ p * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hz p)) (sq_nonneg _)
    have hright : ENNReal.ofReal ((1 / p) * (z ^ p * (Work.Spaces.w z) ^ 2
          * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)))
        = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))) := by
      rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / p), ENNReal.ofReal_mul hzWnn]
    calc ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ENNReal.ofReal ((1 / p) * (z ^ p * (Work.Spaces.w z) ^ 2
            * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))) := hright
      _ ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
            * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
          refine ofReal_setIntegral_le_setLIntegral ?_ ?_
          · exact (((hc.mono (Set.Ioi_subset_Ioi (le_of_lt hz))).aestronglyMeasurable
              measurableSet_Ioi).pow 2).mul
              ((continuous_id.continuousOn.rpow_const
                (fun x hx => Or.inl (ne_of_gt (lt_trans hz hx)))).aestronglyMeasurable
                  measurableSet_Ioi)
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht0 : 0 < t := lt_trans hz ht
            exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht0) _)
  -- (C) the per-`t` bound on the inner weight
  have hper : ∀ t ∈ Set.Ioi (0:ℝ),
      ∫⁻ z in (Set.Ioi 0 ∩ Set.Iio t), ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
        ≤ ENNReal.ofReal (t ^ (p + 1) * (Work.Spaces.w t) ^ 2 / (p - 3)) := by
    intro t ht
    have hset : Set.Ioi (0:ℝ) ∩ Set.Iio t = Set.Ioo 0 t := by
      ext z; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
    rw [hset]
    have h := psi_inner_wt hp4 ht
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 t)] fun z => z ^ p * (Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hz.1) _) (sq_nonneg _)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h.1 hnn]
    exact ENNReal.ofReal_le_ofReal h.2
  -- (D) the key lintegral inequality
  have hP : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2))
      (volume.restrict (Set.Ioi 0)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hcontP.aemeasurable measurableSet_Ioi)
  have hQ : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1)))
      (volume.restrict (Set.Ioi 0)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hcontQ.aemeasurable measurableSet_Ioi)
  have hkey : ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ENNReal.ofReal (1 / (p * (p - 3)))
          * ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    simp only [Work.Spaces.Iz]
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫⁻ z in Set.Ioi 0, (ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
            * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1)))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
          exact hpt z hz
      _ = ENNReal.ofReal (1 / p) * ∫⁻ z in Set.Ioi 0, (ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2)
            * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
      _ = ENNReal.ofReal (1 / p) * ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
            * (∫⁻ z in (Set.Ioi 0 ∩ Set.Iio t), ENNReal.ofReal (z ^ p * (Work.Spaces.w z) ^ 2))) := by
          rw [lintegral_tail_swap hP hQ (fun z => ENNReal.ofReal_lt_top.ne)
            (fun t => ENNReal.ofReal_lt_top.ne)]
      _ ≤ ENNReal.ofReal (1 / p) * ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
            * ENNReal.ofReal (t ^ (p + 1) * (Work.Spaces.w t) ^ 2 / (p - 3))) := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_le_mul' le_rfl (hper t ht)
      _ = ENNReal.ofReal (1 / (p * (p - 3)))
            * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          have hcongr : (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * ENNReal.ofReal (t ^ (p + 1) * (Work.Spaces.w t) ^ 2 / (p - 3)))
              =ᵐ[volume.restrict (Set.Ioi 0)]
              (fun t : ℝ => ENNReal.ofReal (1 / (p - 3))
                * ENNReal.ofReal ((c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht0 : 0 < t := ht
            have h1t : t ^ (-p - 1) * t ^ (p + 1) = 1 := by
              rw [← Real.rpow_add ht0, show -p - 1 + (p + 1) = 0 by ring, Real.rpow_zero]
            rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (c t) ^ 2 * t ^ (-p - 1)),
              ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / (p - 3))]
            congr 1
            rw [show (c t) ^ 2 * t ^ (-p - 1) * (t ^ (p + 1) * (Work.Spaces.w t) ^ 2 / (p - 3))
                = ((c t) ^ 2 * (Work.Spaces.w t) ^ 2) * (t ^ (-p - 1) * t ^ (p + 1)) / (p - 3) by ring,
              h1t]
            ring
          rw [lintegral_congr_ae hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne,
            ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / p)]
          congr 1
          rw [show (1:ℝ) / p * (1 / (p - 3)) = 1 / (p * (p - 3)) by
            rw [div_mul_div_comm, one_mul]]
  -- (E) measurability, integrability and the final bound
  have hTmeas : AEStronglyMeasurable (fun z => ∫ t in Set.Ioi z, c t * t ^ (-p - 1))
      (volume.restrict (Set.Ioi 0)) :=
    aestronglyMeasurable_tailIntegral (hcontF.aestronglyMeasurable measurableSet_Ioi)
  have hAmeas : AEStronglyMeasurable
      (fun z => (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    simp only [Work.Spaces.Iz]
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    have h1' : AEStronglyMeasurable (fun z : ℝ => z ^ p) (volume.restrict (Set.Ioi 0)) :=
      ((continuous_id.continuousOn).rpow_const (fun x hx => Or.inr (le_of_lt hp0))).aestronglyMeasurable
        measurableSet_Ioi
    have h2' : AEStronglyMeasurable
        (fun z : ℝ => z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)))
        (volume.restrict (Set.Ioi 0)) := h1'.mul hTmeas
    have h4' : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (volume.restrict (Set.Ioi 0)) := (continuousOn_w.pow 2).aestronglyMeasurable measurableSet_Ioi
    exact (h2'.pow 2).mul h4'
  have hKlin : ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, (c z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h1
      (ae_of_all _ (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).symm
  have hlin_lt : ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((c z) ^ 2 * (Work.Spaces.w z) ^ 2) ≠ ⊤ := by
    rw [hKlin]; exact ENNReal.ofReal_lt_top.ne
  have hRHS : ENNReal.ofReal (1 / (p * (p - 3)))
      * ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((c z) ^ 2 * (Work.Spaces.w z) ^ 2) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hlin_lt)).ne
  have hfin : ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hkey (lt_top_iff_ne_top.mpr hRHS))
  have hint : MeasureTheory.IntegrableOn
      (fun z => (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAmeas
      (ae_of_all _ (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).mp hfin
  refine ⟨hint, ?_⟩
  have hint_eq : (∫ z in Work.Spaces.Iz,
        (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hAmeas
  rw [hint_eq]
  calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal
      ≤ (ENNReal.ofReal (1 / (p * (p - 3)))
          * ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((c z) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal :=
        ENNReal.toReal_mono hRHS hkey
    _ = (1 / (p * (p - 3))) * ∫ z in Work.Spaces.Iz, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hKlin,
          ENNReal.toReal_ofReal (by positivity)]

end Work.FTS.EllExist.Honesty
