import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.HardyRightTail
import Submission.Work.Elliptic.HardyRightTonelliSwap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem HardyRight (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1:ℝ), HasDerivAt U (U' z) z)
    (hcont : ContinuousAt U 1) (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z => (z * U' z) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z => U z ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1:ℝ), U z ^ 2 ≤ 6 * ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by
  -- Abbreviations.
  set phi : ℝ → ℝ := fun t => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) with hphi
  set G : ℝ → ℝ := fun z => (z * U' z) ^ 2 with hG
  set gg : ℝ → ℝ := fun t => (t * deriv U t) ^ 2 * (Real.sqrt t)⁻¹ with hgg
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (gg t) with hf
  -- `U'` coincides with `deriv U` on `(1,∞)`.
  have hU'eq : ∀ t ∈ Set.Ioi (1:ℝ), U' t = deriv U t :=
    fun t ht => (hderiv t ht).deriv.symm
  -- Measurability of `gg` and `f`.
  have hgg_meas : Measurable gg := by
    rw [hgg]
    exact ((measurable_id.mul (measurable_deriv U)).pow_const 2).mul
      (Real.continuous_sqrt.measurable.inv)
  have hf_meas : Measurable f := by
    rw [hf]; exact ENNReal.continuous_ofReal.measurable.comp hgg_meas
  -- `phi` and `gg` agree on `(1,∞)`.
  have hphigg : ∀ t ∈ Set.Ioi (1:ℝ), phi t = gg t := by
    intro t ht
    have htpos : 0 < t := lt_trans one_pos ht
    simp only [hphi, hgg]
    rw [hU'eq t ht]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_neg htpos.le]
  have htail := HardyRightTail U U' hderiv htend hint
  -- Per-`z` bound in `ℝ≥0∞`.
  have hpt : ∀ z ∈ Set.Ioi (1:ℝ),
      ENNReal.ofReal (U z ^ 2)
        ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) := by
    intro z hz
    have hz1 : (1:ℝ) < z := mem_Ioi.mp hz
    have hzpos : (0:ℝ) < z := lt_trans one_pos hz1
    obtain ⟨hU'int, hbound⟩ := htail z hz
    have hbound' : (U z) ^ 2 ≤ 2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, phi t := hbound
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi z)] phi := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans hzpos (mem_Ioi.mp ht)
      rw [hphi]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg htpos.le _)
    have hmeas : AEStronglyMeasurable phi (volume.restrict (Set.Ioi z)) := by
      have hcongr : gg =ᵐ[volume.restrict (Set.Ioi z)] phi := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hphigg t (lt_trans hz1 (mem_Ioi.mp ht))).symm
      exact hgg_meas.aestronglyMeasurable.congr hcongr
    have hint_eq : (∫ t in Set.Ioi z, phi t) = (∫⁻ t in Set.Ioi z, f t).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [hf]
      congr 1
      exact hphigg t (lt_trans hz1 (mem_Ioi.mp ht))
    have hc : 0 ≤ 2 * z ^ (-(1/2:ℝ)) := by positivity
    calc ENNReal.ofReal (U z ^ 2)
        ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, phi t) :=
          ENNReal.ofReal_le_ofReal hbound'
      _ = ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)) * (∫⁻ t in Set.Ioi z, f t).toReal) := by
          rw [hint_eq]
      _ = ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) *
            ENNReal.ofReal ((∫⁻ t in Set.Ioi z, f t).toReal) :=
          ENNReal.ofReal_mul hc
      _ ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) :=
          mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le bot_le
  have hstep1 : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2))
      ≤ ∫⁻ z in Set.Ioi (1:ℝ),
          ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) :=
    setLIntegral_mono' measurableSet_Ioi hpt
  have hstep2 := HardyRightTonelliSwap f hf_meas
  have hGint : IntegrableOn G (Set.Ioi (1:ℝ)) := by rw [hG]; exact hint
  have hpt2 : ∀ t ∈ Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1))
      ≤ ENNReal.ofReal (4 * G t) := by
    intro t ht
    have ht1 : (1:ℝ) < t := mem_Ioi.mp ht
    have htpos : (0:ℝ) < t := lt_trans one_pos ht1
    have hggnn : 0 ≤ gg t := by
      rw [hgg]
      exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg t))
    rw [hf, ← ENNReal.ofReal_mul hggnn]
    apply ENNReal.ofReal_le_ofReal
    simp only [hgg, hG]
    rw [hU'eq t ht, Real.sqrt_eq_rpow]
    have h1 : (0:ℝ) ≤ t ^ (1/2:ℝ) := Real.rpow_nonneg htpos.le _
    have hpos : 0 < t ^ (1/2:ℝ) := Real.rpow_pos_of_pos htpos _
    have hkey : (t ^ (1/2:ℝ))⁻¹ * (t ^ (1/2:ℝ) - 1) = 1 - (t ^ (1/2:ℝ))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hpos.ne', mul_one]
    have hle1 : 1 - (t ^ (1/2:ℝ))⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr h1)
    have heq : (t * deriv U t) ^ 2 * (t ^ (1/2:ℝ))⁻¹ * (4 * (t ^ (1/2:ℝ) - 1))
        = 4 * (t * deriv U t) ^ 2 * (1 - (t ^ (1/2:ℝ))⁻¹) := by
      rw [← hkey]; ring
    rw [heq]
    calc 4 * (t * deriv U t) ^ 2 * (1 - (t ^ (1/2:ℝ))⁻¹)
        ≤ 4 * (t * deriv U t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hle1 (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 4 * (t * deriv U t) ^ 2 := by ring
  have hstep3 : (∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)))
      ≤ ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) := by
    have h4Gnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun t => 4 * G t) :=
      Filter.Eventually.of_forall (fun t => mul_nonneg (by norm_num) (by rw [hG]; exact sq_nonneg _))
    calc (∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)))
        ≤ ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (4 * G t) :=
          setLIntegral_mono' measurableSet_Ioi hpt2
      _ = ENNReal.ofReal (∫ t in Set.Ioi (1:ℝ), 4 * G t) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hGint.const_mul (4:ℝ)) h4Gnn).symm
      _ = ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) := by
          rw [MeasureTheory.integral_const_mul]
  have hmain : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2))
      ≤ ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) :=
    le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  have hfin : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2)) ≠ ∞ :=
    ne_top_of_lt (lt_of_le_of_lt hmain ENNReal.ofReal_lt_top)
  have hUon : ContinuousOn U (Set.Ioi (1:ℝ)) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hU2_aesm : AEStronglyMeasurable (fun z => U z ^ 2) (volume.restrict (Set.Ioi (1:ℝ))) :=
    (hUon.pow 2).aestronglyMeasurable measurableSet_Ioi
  have hU2_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun z => U z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hintU2 : IntegrableOn (fun z => U z ^ 2) (Set.Ioi (1:ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hU2_aesm hU2_nn).mp hfin
  refine ⟨hintU2, ?_⟩
  have hself : (∫ z in Set.Ioi (1:ℝ), U z ^ 2)
      = (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hU2_nn hU2_aesm
  have hGeq : (∫ z in Set.Ioi (1:ℝ), G z) = ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by
    simp only [hG]
  have hGnn : 0 ≤ ∫ z in Set.Ioi (1:ℝ), G z :=
    integral_nonneg (fun z => by rw [hG]; exact sq_nonneg _)
  calc ∫ z in Set.Ioi (1:ℝ), U z ^ 2
      = (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2)).toReal := hself
    _ ≤ (ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 4 * ∫ z in Set.Ioi (1:ℝ), G z :=
        ENNReal.toReal_ofReal (by linarith)
    _ = 4 * ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by rw [hGeq]
    _ ≤ 6 * ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by
        have hX : 0 ≤ ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by rw [← hGeq]; exact hGnn
        linarith

end Work.Elliptic
