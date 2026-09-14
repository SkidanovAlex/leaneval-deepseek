import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.MeasureTheory

open _root_.MeasureTheory Filter Real Set

theorem ae_restrict_Ioc_sub_mul {t₀ lam T : ℝ} (hlam : 0 < lam) {P : ℝ → Prop}
    (h : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)), P s) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc (t₀ - lam * T) t₀)), P ((t₀ - t) / lam) := by
  have hg_meas : Measurable (fun t : ℝ => (t₀ - t) / lam) := by fun_prop
  have hgc : (fun t : ℝ => (t₀ - t)/lam) ⁻¹' Set.Ioc (0:ℝ) T = Set.Ico (t₀ - lam*T) t₀ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by have h2' := (div_le_iff₀ hlam).mp h2; nlinarith,
             by have h1' := (div_pos_iff_of_pos_right hlam).mp h1; linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [div_pos_iff_of_pos_right hlam]; linarith,
             by rw [div_le_iff₀ hlam]; nlinarith⟩
  have hrestrict : MeasureTheory.volume.restrict (Set.Ioc (t₀ - lam*T) t₀)
      = MeasureTheory.volume.restrict ((fun t : ℝ => (t₀ - t)/lam) ⁻¹' Set.Ioc (0:ℝ) T) := by
    rw [hgc]; exact (MeasureTheory.restrict_Ico_eq_restrict_Ioc).symm
  have hfun : (fun t : ℝ => (t₀ - t)/lam) = (fun t : ℝ => -(lam⁻¹)*t + t₀*lam⁻¹) := by
    funext t; rw [div_eq_mul_inv]; ring
  have hmap_vol : MeasureTheory.Measure.map (fun t : ℝ => (t₀ - t)/lam) MeasureTheory.volume
      = ENNReal.ofReal lam • MeasureTheory.volume := by
    rw [hfun]
    have habs : |(-(lam⁻¹))⁻¹| = lam := by rw [inv_neg, inv_inv, abs_neg, abs_of_pos hlam]
    have hstep1 : MeasureTheory.Measure.map (fun t : ℝ => -(lam⁻¹)*t) MeasureTheory.volume
        = ENNReal.ofReal lam • MeasureTheory.volume := by
      rw [Real.map_volume_mul_left (a := -(lam⁻¹))
        (by rw [neg_ne_zero]; exact inv_ne_zero (ne_of_gt hlam)), habs]
    have hstep2 : MeasureTheory.Measure.map (fun y : ℝ => y + t₀*lam⁻¹)
        (ENNReal.ofReal lam • MeasureTheory.volume) = ENNReal.ofReal lam • MeasureTheory.volume := by
      rw [MeasureTheory.Measure.map_smul, MeasureTheory.map_add_right_eq_self]
    rw [show (fun t : ℝ => -(lam⁻¹)*t + t₀*lam⁻¹)
          = (fun y : ℝ => y + t₀*lam⁻¹) ∘ (fun t : ℝ => -(lam⁻¹)*t) from rfl,
        ← MeasureTheory.Measure.map_map (f := fun t : ℝ => -(lam⁻¹)*t)
          (g := fun y : ℝ => y + t₀*lam⁻¹) (by fun_prop) (by fun_prop),
        hstep1, hstep2]
  have hmap : MeasureTheory.Measure.map (fun t : ℝ => (t₀ - t)/lam)
      (MeasureTheory.volume.restrict (Set.Ioc (t₀ - lam*T) t₀))
      = ENNReal.ofReal lam • MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T) := by
    rw [hrestrict, ← MeasureTheory.Measure.restrict_map hg_meas measurableSet_Ioc, hmap_vol,
        MeasureTheory.Measure.restrict_smul]
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (fun t : ℝ => (t₀ - t)/lam)
      (MeasureTheory.volume.restrict (Set.Ioc (t₀ - lam*T) t₀))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)) :=
    ⟨hg_meas, by rw [hmap]; exact MeasureTheory.Measure.smul_absolutelyContinuous⟩
  exact hqmp.ae h

end Commons.MeasureTheory