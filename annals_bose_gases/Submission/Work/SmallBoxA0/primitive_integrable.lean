import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.SmallBoxA0.ae_stronglyMeasurable_rep
import Submission.Work.SmallBoxA0.lintegral_Ioo_Ioo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Set

/-- The restriction of Lebesgue measure to `Ioc r R` and to `Ioo r R` agree. -/
private lemma restrict_Ioc_Ioo (r R : ℝ) :
    volume.restrict (Ioc r R) = volume.restrict (Ioo r R) := by
  apply Measure.restrict_congr_set
  filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := R))] with x hx
  apply propext
  show r < x ∧ x ≤ R ↔ r < x ∧ x < R
  exact ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 (by simpa using hx)⟩,
         fun h => ⟨h.1, h.2.le⟩⟩

theorem primitive_integrable {R : ℝ} (hR : 0 < R) {u : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn (fun t : ℝ => t * u t) (Set.Ioo (0 : ℝ) R)) :
    IntervalIntegrable (fun r : ℝ => ∫ t in r..R, u t) volume 0 R := by
  obtain ⟨u', hu'_sm, hu'_ae⟩ := ae_stronglyMeasurable_rep (R := R) hu
  have hg : Integrable (fun t : ℝ => t * u t) (volume.restrict (Ioo (0:ℝ) R)) := hu
  -- ### The joint kernel
  set Φ : ℝ × ℝ → ℝ :=
    fun p => if 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ R then u' p.2 else 0 with hΦ
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ R} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  have hΦ_ae : AEStronglyMeasurable Φ (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => u' p.2) (volume.prod volume) :=
      hu'_sm.aestronglyMeasurable.comp_snd
    have hfun : Φ = {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ R}.indicator
        (fun p => u' p.2) := by
      rw [hΦ]
      funext p
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hfun]
    exact h1.indicator hS
  -- ### Measurability of the primitive
  have hproj_ae : AEStronglyMeasurable (fun r : ℝ => ∫ t, Φ (r, t)) volume :=
    hΦ_ae.integral_prod_right'
  have hproj_ae' : AEStronglyMeasurable (fun r : ℝ => ∫ t, Φ (r, t))
      (volume.restrict (Ioo (0:ℝ) R)) :=
    hproj_ae.mono_measure Measure.restrict_le_self
  have hproj_eq : (fun r : ℝ => ∫ t, Φ (r, t))
      =ᵐ[volume.restrict (Ioo (0:ℝ) R)] (fun r : ℝ => ∫ t in r..R, u t) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with r hr
    have hr0 : 0 < r := hr.1
    have hIocle : volume.restrict (Ioc r R) ≤ volume.restrict (Ioo (0:ℝ) R) := by
      rw [restrict_Ioc_Ioo r R]
      exact Measure.restrict_mono_set volume (Ioo_subset_Ioo hr.1.le le_rfl)
    have hae : u =ᵐ[volume.restrict (Ioc r R)] u' :=
      hu'_ae.symm.filter_mono (ae_mono hIocle)
    have h1 : (fun t => Φ (r, t)) = (Ioc r R).indicator u' := by
      rw [hΦ]
      funext t
      dsimp only
      rw [Set.indicator_apply]
      simp only [Set.mem_Ioc]
      by_cases h : r < t ∧ t ≤ R
      · rw [if_pos h, if_pos ⟨hr0, h⟩]
      · rw [if_neg h, if_neg (fun hh => h hh.2)]
    rw [h1, intervalIntegral.integral_of_le hr.2.le,
      MeasureTheory.integral_indicator measurableSet_Ioc]
    exact (MeasureTheory.integral_congr_ae hae).symm
  have hHae : AEStronglyMeasurable (fun r : ℝ => ∫ t in r..R, u t)
      (volume.restrict (Ioo (0:ℝ) R)) := hproj_ae'.congr hproj_eq
  -- ### Finiteness
  have hHfin : HasFiniteIntegral (fun r : ℝ => ∫ t in r..R, u t)
      (volume.restrict (Ioo (0:ℝ) R)) := by
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ r in Ioo (0:ℝ) R, ‖∫ t in r..R, u t‖ₑ
        ≤ ∫⁻ r in Ioo (0:ℝ) R, (∫⁻ t in Ioo r R, ‖u t‖ₑ) := by
          apply lintegral_mono_ae
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
          filter_upwards with r hr
          have h1 : ‖∫ t in r..R, u t‖ₑ ≤ ∫⁻ t in Ioc r R, ‖u t‖ₑ := by
            rw [intervalIntegral.integral_of_le hr.2.le]
            exact enorm_integral_le_lintegral_enorm u
          rwa [restrict_Ioc_Ioo r R] at h1
      _ = ∫⁻ r in Ioo (0:ℝ) R, (∫⁻ t in Ioo r R, ‖u' t‖ₑ) := by
          apply lintegral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
          apply lintegral_congr_ae
          have hle : volume.restrict (Ioo r R) ≤ volume.restrict (Ioo (0:ℝ) R) :=
            Measure.restrict_mono_set volume (Ioo_subset_Ioo hr.1.le le_rfl)
          filter_upwards [(hu'_ae.filter_mono (ae_mono hle)).symm] with t ht
          rw [ht]
      _ = ∫⁻ t in Ioo (0:ℝ) R, ‖u' t‖ₑ * ENNReal.ofReal t :=
          lintegral_Ioo_Ioo hR hu'_sm.enorm.aemeasurable
      _ = ∫⁻ t in Ioo (0:ℝ) R, ‖t * u t‖ₑ := by
          apply lintegral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioo, hu'_ae] with t ht ht'
          have hlen : ‖(t:ℝ)‖ₑ = ENNReal.ofReal t := Real.enorm_eq_ofReal ht.1.le
          rw [enorm_mul, hlen, ← ht']
          exact mul_comm _ _
      _ < ⊤ := by
          have h := hg.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_enorm] at h
          exact h
  -- ### Assembly
  have hHint : IntegrableOn (fun r : ℝ => ∫ t in r..R, u t) (Ioo (0:ℝ) R) := ⟨hHae, hHfin⟩
  have hmeasure : volume.restrict (Ioc (0:ℝ) R) = volume.restrict (Ioo (0:ℝ) R) := by
    apply Measure.restrict_congr_set
    filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := R))] with x hx
    apply propext
    show (0:ℝ) < x ∧ x ≤ R ↔ 0 < x ∧ x < R
    exact ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 (by simpa using hx)⟩,
           fun h => ⟨h.1, h.2.le⟩⟩
  have hHint' : IntegrableOn (fun r : ℝ => ∫ t in r..R, u t) (Ioc (0:ℝ) R) := by
    show Integrable (fun r : ℝ => ∫ t in r..R, u t) (volume.restrict (Ioc (0:ℝ) R))
    rw [hmeasure]
    exact hHint
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
  exact hHint'

end Work.SmallBoxA0
