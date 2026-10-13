import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory

/-- Cauchy–Schwarz in squared form for nonnegative real `L²` functions. -/
theorem integral_mul_sq_le_sq_mul_sq_aux {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) {f g : α → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ)
    (hfm : 0 ≤ᵐ[μ] f) (hgm : 0 ≤ᵐ[μ] g) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf' : MeasureTheory.MemLp f (ENNReal.ofReal (2:ℝ)) μ := by
    rwa [ENNReal.ofReal_ofNat]
  have hg' : MeasureTheory.MemLp g (ENNReal.ofReal (2:ℝ)) μ := by
    rwa [ENNReal.ofReal_ofNat]
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq hfm hgm hf' hg'
  have hf2 : (∫ x, f x ^ (2:ℝ) ∂μ) = ∫ x, f x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.rpow_ofNat (f x) 2)
  have hg2 : (∫ x, g x ^ (2:ℝ) ∂μ) = ∫ x, g x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.rpow_ofNat (g x) 2)
  rw [hf2, hg2] at hholder
  have hnonneg : 0 ≤ ∫ x, f x * g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hfm, hgm] with x hx hy
    exact mul_nonneg hx hy
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hfm] with x hx
    exact pow_nonneg hx 2
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hgm] with x hx
    exact pow_nonneg hx 2
  calc (∫ x, f x * g x ∂μ) ^ 2
      ≤ ((∫ x, f x ^ 2 ∂μ) ^ (1/2:ℝ) * (∫ x, g x ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 :=
        pow_le_pow_left₀ hnonneg hholder 2
    _ = (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
        rw [← Real.mul_rpow hA hB, ← Real.sqrt_eq_rpow, Real.sq_sqrt (mul_nonneg hA hB)]

theorem tail_l2_cauchy_schwarz (z : ℝ) (hz : 0 < z) (φ : ℝ → ℝ)
    (hφmeas : MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.volume.restrict (Set.Ioi z)))
    (hφint : MeasureTheory.IntegrableOn φ (Set.Ioi z))
    (hφG : MeasureTheory.IntegrableOn (fun t : ℝ => (t * φ t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi z)) :
    (∫ t in Set.Ioi z, φ t) ^ 2
      ≤ (∫ t in Set.Ioi z, (t * φ t) ^ 2 * t ^ (-(1/2:ℝ))) * (2 * z ^ (-(1/2:ℝ))) := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi z) with hμ
  set a : ℝ → ℝ := fun t => |t * φ t| * t ^ (-(1/4:ℝ)) with ha
  set b : ℝ → ℝ := fun t => t ^ (-(3/4:ℝ)) with hb
  have ht_pos : ∀ t ∈ Set.Ioi z, 0 < t := fun t ht => hz.trans ht
  have hab_pt : ∀ t ∈ Set.Ioi z, a t * b t = |φ t| := by
    intro t ht
    have ht0 : 0 < t := ht_pos t ht
    have h1 : t ^ (-(1/4:ℝ)) * t ^ (-(3/4:ℝ)) = t ^ (-1:ℝ) := by
      rw [← Real.rpow_add ht0]; norm_num
    have h2 : (t * φ t) * t⁻¹ = φ t := by
      rw [mul_assoc, mul_comm (φ t) t⁻¹, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht0), one_mul]
    have h3 : |φ t| = |t * φ t| * t⁻¹ := by
      calc |φ t| = |(t * φ t) * t⁻¹| := by rw [h2]
        _ = |t * φ t| * |t⁻¹| := by rw [abs_mul]
        _ = |t * φ t| * t⁻¹ := by rw [abs_of_pos (inv_pos.mpr ht0)]
    simp only [ha, hb]
    calc |t * φ t| * t ^ (-(1/4:ℝ)) * t ^ (-(3/4:ℝ))
        = |t * φ t| * (t ^ (-(1/4:ℝ)) * t ^ (-(3/4:ℝ))) := by rw [mul_assoc]
      _ = |t * φ t| * t ^ (-1:ℝ) := by rw [h1]
      _ = |t * φ t| * t⁻¹ := by rw [Real.rpow_neg_one]
      _ = |φ t| := h3.symm
  have ha2_pt : ∀ t ∈ Set.Ioi z, a t ^ 2 = (t * φ t) ^ 2 * t ^ (-(1/2:ℝ)) := by
    intro t ht
    have ht0 : 0 < t := ht_pos t ht
    have hkey : (t ^ (-(1/4:ℝ)))^2 = t ^ (-(1/2:ℝ)) := by
      rw [sq, ← Real.rpow_add ht0, show -(1/4:ℝ) + -(1/4:ℝ) = -(1/2:ℝ) by norm_num]
    simp only [ha]
    calc (|t * φ t| * t ^ (-(1/4:ℝ)))^2
        = |t * φ t|^2 * (t ^ (-(1/4:ℝ)))^2 := by ring
      _ = (t * φ t)^2 * t ^ (-(1/2:ℝ)) := by rw [sq_abs, hkey]
  have hb2_pt : ∀ t ∈ Set.Ioi z, b t ^ 2 = t ^ (-(3/2:ℝ)) := by
    intro t ht
    have ht0 : 0 < t := ht_pos t ht
    simp only [hb]
    rw [sq, ← Real.rpow_add ht0, show -(3/4:ℝ) + -(3/4:ℝ) = -(3/2:ℝ) by norm_num]
  have hab : ∫ x, a x * b x ∂μ = ∫ x, |φ x| ∂μ := by
    rw [hμ]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hab_pt t ht
  have ha2 : ∫ x, a x ^ 2 ∂μ = ∫ x, (x * φ x) ^ 2 * x ^ (-(1/2:ℝ)) ∂μ := by
    rw [hμ]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ha2_pt t ht
  have hb2 : ∫ x, b x ^ 2 ∂μ = ∫ x, x ^ (-(3/2:ℝ)) ∂μ := by
    rw [hμ]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hb2_pt t ht
  have hbint : ∫ x, x ^ (-(3/2:ℝ)) ∂μ = 2 * z ^ (-(1/2:ℝ)) := by
    rw [hμ]
    rw [integral_Ioi_rpow_of_lt (a := -(3/2:ℝ)) (by norm_num) hz]
    rw [show (-(3/2:ℝ)) + 1 = -(1/2:ℝ) by norm_num]
    ring
  have hmeas_a : MeasureTheory.AEStronglyMeasurable a μ := by
    rw [hμ]
    have h1 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |t * φ t|)
        (MeasureTheory.volume.restrict (Set.Ioi z)) := by
      have h2 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t * φ t)
          (MeasureTheory.volume.restrict (Set.Ioi z)) :=
        (continuous_id.aestronglyMeasurable (μ := MeasureTheory.volume.restrict (Set.Ioi z))).mul hφmeas
      simpa only [Real.norm_eq_abs] using h2.norm
    have h3 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (-(1/4:ℝ)))
        (MeasureTheory.volume.restrict (Set.Ioi z)) :=
      (ContinuousOn.rpow_const (f := id) (s := Set.Ioi z) (p := -(1/4:ℝ)) continuousOn_id
          (fun t ht => Or.inl (ne_of_gt (hz.trans ht)))).aestronglyMeasurable measurableSet_Ioi
    have h4 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |t * φ t| * t ^ (-(1/4:ℝ)))
        (MeasureTheory.volume.restrict (Set.Ioi z)) := h1.mul h3
    simpa only [ha] using h4
  have hmeas_b : MeasureTheory.AEStronglyMeasurable b μ := by
    rw [hμ, hb]
    exact (ContinuousOn.rpow_const (f := id) (s := Set.Ioi z) (p := -(3/4:ℝ)) continuousOn_id
        (fun t ht => Or.inl (ne_of_gt (hz.trans ht)))).aestronglyMeasurable measurableSet_Ioi
  have hint_a2 : MeasureTheory.Integrable (fun x => a x ^ 2) μ := by
    rw [hμ]
    refine hφG.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (ha2_pt t ht).symm
  have hint_b2 : MeasureTheory.Integrable (fun x => b x ^ 2) μ := by
    rw [hμ]
    refine (integrableOn_Ioi_rpow_of_lt (a := -(3/2:ℝ)) (by norm_num) hz).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hb2_pt t ht).symm
  have hmem_a : MeasureTheory.MemLp a 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeas_a).mpr hint_a2
  have hmem_b : MeasureTheory.MemLp b 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeas_b).mpr hint_b2
  have ha_nonneg : 0 ≤ᵐ[μ] a := by
    rw [hμ]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [ha]
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (le_of_lt (ht_pos t ht)) _)
  have hb_nonneg : 0 ≤ᵐ[μ] b := by
    rw [hμ]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [hb]
    exact Real.rpow_nonneg (le_of_lt (ht_pos t ht)) _
  have hcs := integral_mul_sq_le_sq_mul_sq_aux μ hmem_a hmem_b ha_nonneg hb_nonneg
  have habs : |∫ t, φ t ∂μ| ≤ ∫ t, |φ t| ∂μ := abs_integral_le_integral_abs
  calc (∫ t, φ t ∂μ) ^ 2
      = (|∫ t, φ t ∂μ|) ^ 2 := (sq_abs (∫ t, φ t ∂μ)).symm
    _ ≤ (∫ t, |φ t| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = (∫ t, a t * b t ∂μ) ^ 2 := by rw [← hab]
    _ ≤ (∫ t, a t ^ 2 ∂μ) * (∫ t, b t ^ 2 ∂μ) := hcs
    _ = (∫ t, (t * φ t) ^ 2 * t ^ (-(1/2:ℝ)) ∂μ) * (∫ t, t ^ (-(3/2:ℝ)) ∂μ) := by rw [ha2, hb2]
    _ = (∫ t, (t * φ t) ^ 2 * t ^ (-(1/2:ℝ)) ∂μ) * (2 * z ^ (-(1/2:ℝ))) := by rw [hbint]

end Work.Elliptic
