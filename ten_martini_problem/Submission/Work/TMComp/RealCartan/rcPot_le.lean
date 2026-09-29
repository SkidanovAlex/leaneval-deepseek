import Mathlib
import Submission.Work.TMComp.RealCartanDefs
import Submission.Work.TMComp.RealCartan.rcLogKernel_int
import Submission.Work.TMComp.RealCartan.rcLogKernel_integrable
import Submission.Work.TMComp.RealCartan.rcNormKernel_integrable
import Submission.Work.TMComp.RealCartan.rcLogPot_integrable

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace Work.TMComp.RealCartan

lemma log_div_le_max {R a : ℝ} (ha : 0 < a) :
    Real.log (R / a) ≤ Real.log R + max (Real.log (1 / a)) 0 := by
  rcases eq_or_ne R 0 with hR | hR
  · subst hR; simp
  · rw [Real.log_div hR (ne_of_gt ha), one_div, Real.log_inv]
    have h := le_max_left (-Real.log a) 0
    linarith

lemma max_log_one_le {ρ a : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 ≤ a) :
    max (Real.log (1 / a)) 0 ≤ Real.log (1 / ρ) + max (Real.log (ρ / a)) 0 := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hlog1 : 0 ≤ Real.log (1 / ρ) := by
    rw [one_div]; exact Real.log_nonneg ((one_le_inv₀ hρ).mpr hρ1)
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : Real.log (1 / (0:ℝ)) = 0 := by simp
    have h0' : Real.log (ρ / (0:ℝ)) = 0 := by simp
    rw [h0, h0']
    simp only [max_self, add_zero]
    exact hlog1
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hane : a ≠ 0 := ne_of_gt hapos
    rcases lt_or_ge a ρ with hlt | hge
    · have h2 : Real.log (1 / a) = Real.log (1 / ρ) + Real.log (ρ / a) := by
        rw [Real.log_div hρne hane, one_div, one_div, Real.log_inv, Real.log_inv]; ring
      rw [h2, max_le_iff]
      exact ⟨add_le_add (le_refl (Real.log (1 / ρ))) (le_max_left (Real.log (ρ / a)) 0),
        add_nonneg hlog1 (le_max_right (Real.log (ρ / a)) 0)⟩
    · have hle : Real.log (1 / a) ≤ Real.log (1 / ρ) := by
        apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le hρ hge
      calc max (Real.log (1 / a)) 0 ≤ max (Real.log (1 / ρ)) 0 := max_le_max hle le_rfl
        _ = Real.log (1 / ρ) := max_eq_left hlog1
        _ ≤ Real.log (1 / ρ) + max (Real.log (ρ / a)) 0 := le_add_of_nonneg_right (le_max_right _ _)

lemma norm_kernel_ae_le (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (fun t : ℝ => max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      ≤ᵐ[MeasureTheory.volume] (fun t : ℝ => max (Real.log (ρ / |t - z.re|)) 0) := by
  change ∀ᵐ t : ℝ ∂MeasureTheory.volume,
    max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 ≤ max (Real.log (ρ / |t - z.re|)) 0
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null _ (by simp : MeasureTheory.volume {z.re} = 0)
  intro t ht
  simp only [Set.mem_ofPred_eq, not_le] at ht
  by_contra hmem
  have htne : t ≠ z.re := by simpa [Set.mem_singleton_iff] using hmem
  have htne' : t - z.re ≠ 0 := fun h => htne (sub_eq_zero.mp h)
  have hm : 0 < |t - z.re| := abs_pos.mpr htne'
  have hmle : |t - z.re| ≤ ‖z - (t:ℂ)‖ := by
    have h := Complex.abs_re_le_norm (z - (t:ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    rwa [abs_sub_comm] at h
  have hnpos : 0 < ‖z - (t:ℂ)‖ := lt_of_lt_of_le hm hmle
  have hle : Real.log (ρ / ‖z - (t:ℂ)‖) ≤ Real.log (ρ / |t - z.re|) := by
    rw [Real.log_div (ne_of_gt hρ) (ne_of_gt hnpos), Real.log_div (ne_of_gt hρ) (ne_of_gt hm)]
    have h2 : Real.log |t - z.re| ≤ Real.log ‖z - (t:ℂ)‖ := Real.log_le_log hm hmle
    linarith
  have hfin : max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 ≤ max (Real.log (ρ / |t - z.re|)) 0 :=
    max_le_max hle le_rfl
  exact absurd hfin (not_le.mpr ht)

lemma key_bound {B : Set ℝ} {x₀ ρ : ℝ} (hB : B ⊆ Set.Icc (x₀ - ρ) (x₀ + ρ))
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (z : ℂ) :
    ∫ t in B, max (Real.log (1 / ‖z - (t:ℂ)‖)) 0 ≤ 2 * ρ * (Real.log (1 / ρ) + 1) := by
  have hρ1' : ρ ≤ 1 := by linarith
  have hlog1 : 0 ≤ Real.log (1 / ρ) := by
    rw [one_div]; exact Real.log_nonneg ((one_le_inv₀ hρ).mpr hρ1')
  have hBfin : MeasureTheory.volume B ≠ ∞ := by
    have hle : MeasureTheory.volume B ≤ MeasureTheory.volume (Set.Icc (x₀ - ρ) (x₀ + ρ)) :=
      measure_mono hB
    rw [Real.volume_Icc] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hres : (MeasureTheory.volume.restrict B) Set.univ ≠ ∞ := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hBfin
  have hInt_ws : Integrable (fun t : ℝ => max (Real.log (ρ / |t - z.re|)) 0) MeasureTheory.volume :=
    rcLogKernel_integrable hρ
  have hInt_wz_B : Integrable (fun t : ℝ => max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) := (rcNormKernel_integrable z hρ).integrableOn
  have hInt_const_B : Integrable (fun _ : ℝ => Real.log (1 / ρ)) (MeasureTheory.volume.restrict B) := by
    simpa using (integrableOn_const (C := Real.log (1 / ρ)) (s := Set.univ)
      (μ := MeasureTheory.volume.restrict B) hres)
  have hInt_dom_B : Integrable (fun t : ℝ =>
      Real.log (1 / ρ) + max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) := hInt_const_B.add hInt_wz_B
  have hstep2 : ∫ t in B, max (Real.log (1 / ‖z - (t:ℂ)‖)) 0
      ≤ ∫ t in B, (Real.log (1 / ρ) + max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0) := by
    apply integral_mono_of_nonneg
    · filter_upwards with t; exact le_max_right _ _
    · exact hInt_dom_B
    · filter_upwards with t
      exact max_log_one_le hρ hρ1' (norm_nonneg _)
  have hconst : ∫ t in B, Real.log (1 / ρ) = (MeasureTheory.volume B).toReal * Real.log (1 / ρ) := by
    rw [MeasureTheory.integral_const, smul_eq_mul, MeasureTheory.Measure.real_def]
    congr 1
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hstep3 : ∫ t in B, (Real.log (1 / ρ) + max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      = (MeasureTheory.volume B).toReal * Real.log (1 / ρ)
        + ∫ t in B, max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 := by
    rw [MeasureTheory.integral_add hInt_const_B hInt_wz_B, hconst]
  have hstep4 : ∫ t in B, max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 ≤ 2 * ρ := by
    have h1 : ∫ t in B, max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0
        ≤ ∫ t in (Set.univ : Set ℝ), max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 := by
      apply setIntegral_mono_set ((rcNormKernel_integrable z hρ).integrableOn (s := (Set.univ : Set ℝ)))
      · filter_upwards with t; exact le_max_right _ _
      · exact Filter.Eventually.of_forall (fun x _ => trivial)
    have h1' : ∫ t in (Set.univ : Set ℝ), max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0
        = ∫ t : ℝ, max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 := MeasureTheory.setIntegral_univ
    have h2 : ∫ t : ℝ, max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0
        ≤ ∫ t : ℝ, max (Real.log (ρ / |t - z.re|)) 0 := by
      apply integral_mono_of_nonneg
      · filter_upwards with t; exact le_max_right _ _
      · exact hInt_ws
      · exact norm_kernel_ae_le z hρ
    linarith [h1, h1', h2, rcLogKernel_int (s := z.re) hρ]
  have hvolB : (MeasureTheory.volume B).toReal ≤ 2 * ρ := by
    have hle : MeasureTheory.volume B ≤ ENNReal.ofReal (2 * ρ) := by
      calc MeasureTheory.volume B ≤ MeasureTheory.volume (Set.Icc (x₀ - ρ) (x₀ + ρ)) := measure_mono hB
        _ = ENNReal.ofReal ((x₀ + ρ) - (x₀ - ρ)) := Real.volume_Icc
        _ = ENNReal.ofReal (2 * ρ) := by ring_nf
    calc (MeasureTheory.volume B).toReal
        ≤ (ENNReal.ofReal (2 * ρ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 2 * ρ := ENNReal.toReal_ofReal (by linarith)
  calc ∫ t in B, max (Real.log (1 / ‖z - (t:ℂ)‖)) 0
      ≤ ∫ t in B, (Real.log (1 / ρ) + max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0) := hstep2
    _ = (MeasureTheory.volume B).toReal * Real.log (1 / ρ)
        + ∫ t in B, max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 := hstep3
    _ ≤ 2 * ρ * Real.log (1 / ρ) + 2 * ρ := by
        have hmul := mul_le_mul_of_nonneg_right hvolB hlog1
        linarith
    _ = 2 * ρ * (Real.log (1 / ρ) + 1) := by ring

theorem rcPot_le {B : Set ℝ} {x₀ ρ R : ℝ} (hB : B ⊆ Set.Icc (x₀ - ρ) (x₀ + ρ))
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∀ z : ℂ, Work.TMComp.RC.logPot B R z
      ≤ (MeasureTheory.volume B).toReal * Real.log R + 2 * ρ * (Real.log (1 / ρ) + 1) := by
  intro z
  have hρ1' : ρ ≤ 1 := by linarith
  have hlog1 : 0 ≤ Real.log (1 / ρ) := by
    rw [one_div]; exact Real.log_nonneg ((one_le_inv₀ hρ).mpr hρ1')
  have hkey := key_bound hB hρ hρ1 z
  have hBfin : MeasureTheory.volume B ≠ ∞ := by
    have hle : MeasureTheory.volume B ≤ MeasureTheory.volume (Set.Icc (x₀ - ρ) (x₀ + ρ)) :=
      measure_mono hB
    rw [Real.volume_Icc] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hres : (MeasureTheory.volume.restrict B) Set.univ ≠ ∞ := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hBfin
  have hae0 : (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖))
      ≤ᵐ[MeasureTheory.volume]
        (fun t : ℝ => Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0) := by
    change ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      Real.log (R / ‖z - (t:ℂ)‖) ≤ Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ (by simp : MeasureTheory.volume {z.re} = 0)
    intro t ht
    simp only [Set.mem_ofPred_eq, not_le] at ht
    by_contra hmem
    have htne : t ≠ z.re := by simpa [Set.mem_singleton_iff] using hmem
    have hn : ‖z - (t:ℂ)‖ ≠ 0 := by
      intro h
      have hz : z = (t:ℂ) := sub_eq_zero.mp (norm_eq_zero.mp h)
      have : z.re = t := by rw [hz]; simp
      exact htne this.symm
    have hpos : 0 < ‖z - (t:ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hlog : Real.log (R / ‖z - (t:ℂ)‖) ≤ Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0 :=
      log_div_le_max hpos
    exact absurd hlog (not_le.mpr ht)
  have hae : (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖))
      ≤ᵐ[MeasureTheory.volume.restrict B]
        (fun t : ℝ => Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0) :=
    MeasureTheory.ae_mono Measure.restrict_le_self hae0
  have hInt_wz_B : Integrable (fun t : ℝ => max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) := (rcNormKernel_integrable z hρ).integrableOn
  have hInt_const_B : Integrable (fun _ : ℝ => Real.log (1 / ρ)) (MeasureTheory.volume.restrict B) := by
    simpa using (integrableOn_const (C := Real.log (1 / ρ)) (s := Set.univ)
      (μ := MeasureTheory.volume.restrict B) hres)
  have hInt_constR_B : Integrable (fun _ : ℝ => Real.log R) (MeasureTheory.volume.restrict B) := by
    simpa using (integrableOn_const (C := Real.log R) (s := Set.univ)
      (μ := MeasureTheory.volume.restrict B) hres)
  have hInt_dom_B : Integrable (fun t : ℝ =>
      Real.log (1 / ρ) + max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) := hInt_const_B.add hInt_wz_B
  have hAESM : AEStronglyMeasurable (fun t : ℝ => max (Real.log (1 / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hIntpsi : Integrable (fun t : ℝ => max (Real.log (1 / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) :=
    Integrable.mono' hInt_dom_B hAESM (Filter.Eventually.of_forall (fun t => by
      have := max_log_one_le hρ hρ1' (norm_nonneg (z - (t:ℂ)))
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact this))
  have hIntg : Integrable (fun t : ℝ => Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0)
      (MeasureTheory.volume.restrict B) := hInt_constR_B.add hIntpsi
  have hIntf : Integrable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖))
      (MeasureTheory.volume.restrict B) :=
    (rcLogPot_integrable z R (x₀ - ρ) (x₀ + ρ)).mono_set hB
  have hmain := integral_mono_ae hIntf hIntg hae
  have hgval : ∫ t in B, (Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0)
      = (MeasureTheory.volume B).toReal * Real.log R
        + ∫ t in B, max (Real.log (1 / ‖z - (t:ℂ)‖)) 0 := by
    rw [MeasureTheory.integral_add hInt_constR_B hIntpsi,
      MeasureTheory.integral_const, smul_eq_mul, MeasureTheory.Measure.real_def]
    congr 1
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [Work.TMComp.RC.logPot]
  calc ∫ t in B, Real.log (R / ‖z - (t:ℂ)‖)
      ≤ ∫ t in B, (Real.log R + max (Real.log (1 / ‖z - (t:ℂ)‖)) 0) := hmain
    _ = (MeasureTheory.volume B).toReal * Real.log R
        + ∫ t in B, max (Real.log (1 / ‖z - (t:ℂ)‖)) 0 := hgval
    _ ≤ (MeasureTheory.volume B).toReal * Real.log R + 2 * ρ * (Real.log (1 / ρ) + 1) := by
        linarith [hkey]

end Work.TMComp.RealCartan
