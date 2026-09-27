import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.vol_inter_lower
import Submission.Work.EKLC8Core.mass_sub_interval
import Submission.Work.EKLC8Core.vol_preimage_affine_sub_Icc

namespace Work.EKLC8Core

open MeasureTheory

theorem step7_measure {T θ ε η : ℝ} (hT : 0 < T) (hθ : 4 * T ≤ θ) (hθ' : θ ≤ 6 * T)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    {Q₁ Q₂ : Set ℝ} (hQ₁m : MeasurableSet Q₁) (hQ₂m : MeasurableSet Q₂)
    (hQ₁ : (1 - ε) * T ≤ vol (Q₁ ∩ Set.Icc 0 T))
    (hQ₂ : (1 - ε) * (4 * T) ≤ vol (Q₂ ∩ Set.Icc 0 (4 * T))) :
    (1 - 9 * ε) * T ≤ vol ({τ : ℝ | τ ∈ Q₁ ∧ (θ + (2 - η) * τ) / 2 ∈ Q₂} ∩ Set.Icc 0 T) := by
  set a : ℝ := (2 - η) / 2 with ha
  set b : ℝ := θ / 2 with hb
  have ha_pos : 0 < a := by rw [ha]; linarith
  have ha_ge : (1 : ℝ) / 2 ≤ a := by rw [ha]; linarith
  have ha_le : a ≤ 1 := by rw [ha]; linarith
  have hb_nonneg : 0 ≤ b := by rw [hb]; linarith
  have hb_le : b + a * T ≤ 4 * T := by
    rw [ha, hb]
    have h2 : (2 - η) / 2 * T ≤ T := by
      have h3 : (2 - η) / 2 ≤ 1 := by linarith
      nlinarith [hT, h3]
    linarith
  have hf : ∀ τ : ℝ, a * τ + b = (θ + (2 - η) * τ) / 2 := by
    intro τ; rw [ha, hb]; ring
  have hseteq : {τ : ℝ | τ ∈ Q₁ ∧ (θ + (2 - η) * τ) / 2 ∈ Q₂}
      = Q₁ ∩ (fun τ : ℝ => a * τ + b) ⁻¹' Q₂ := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hf τ]
  rw [hseteq]
  have hpq : b ≤ b + a * T := by
    have h2 : 0 ≤ a * T := mul_nonneg ha_pos.le hT.le
    linarith
  have hsub : Set.Icc b (b + a * T) ⊆ Set.Icc 0 (4 * T) :=
    fun x hx => ⟨le_trans hb_nonneg hx.1, le_trans hx.2 hb_le⟩
  -- The density of `Q₂` on the image interval.
  have hD : a * T - 4 * ε * T ≤ vol (Q₂ ∩ Set.Icc b (b + a * T)) := by
    have hBm : MeasurableSet (Q₂ ∩ Set.Icc 0 (4 * T)) := hQ₂m.inter measurableSet_Icc
    have hdens : (1 - ε) * ((4 * T) - 0) ≤ vol (Q₂ ∩ Set.Icc 0 (4 * T)) := by
      simpa using hQ₂
    have hres := mass_sub_interval (L := 0) (R := 4 * T) (p := b) (q := b + a * T)
      hb_nonneg hpq hb_le hBm Set.inter_subset_right hε.le hdens
    have hset : (Q₂ ∩ Set.Icc 0 (4 * T)) ∩ Set.Icc b (b + a * T)
        = Q₂ ∩ Set.Icc b (b + a * T) := by
      rw [Set.inter_assoc, Set.inter_eq_right.mpr hsub]
    rw [hset] at hres
    linarith
  -- Pulling the density back to `[0,T]`.
  have hC : T - 8 * ε * T ≤ vol ((fun τ : ℝ => a * τ + b) ⁻¹' Q₂ ∩ Set.Icc 0 T) := by
    rw [vol_preimage_affine_sub_Icc (a := a) (b := b) (T := T) ha_pos Q₂]
    have hainv : a⁻¹ * a = 1 := inv_mul_cancel₀ ha_pos.ne'
    have h2 : T - 8 * ε * T ≤ a⁻¹ * (a * T - 4 * ε * T) := by
      have hstep : a⁻¹ * (1 / 2) ≤ a⁻¹ * a :=
        mul_le_mul_of_nonneg_left ha_ge (inv_nonneg.mpr ha_pos.le)
      rw [hainv] at hstep
      have hainv_le : a⁻¹ ≤ 2 := by linarith
      have hmul : 4 * ε * T * a⁻¹ ≤ 4 * ε * T * 2 :=
        mul_le_mul_of_nonneg_left hainv_le (by positivity)
      have hexp : a⁻¹ * (a * T - 4 * ε * T) = T - 4 * ε * T * a⁻¹ := by
        rw [mul_sub]
        have h1 : a⁻¹ * (a * T) = T := by rw [← mul_assoc, hainv, one_mul]
        rw [h1]; ring
      rw [hexp]; linarith
    have h3 : a⁻¹ * (a * T - 4 * ε * T) ≤ a⁻¹ * vol (Q₂ ∩ Set.Icc b (b + a * T)) :=
      mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr ha_pos.le)
    linarith
  -- Squeeze the two densities together on `[0,T]`.
  have hAm : MeasurableSet (Q₁ ∩ Set.Icc 0 T) := hQ₁m.inter measurableSet_Icc
  have hfm : Measurable (fun τ : ℝ => a * τ + b) := by fun_prop
  have hCm : MeasurableSet ((fun τ : ℝ => a * τ + b) ⁻¹' Q₂ ∩ Set.Icc 0 T) :=
    (hQ₂m.preimage hfm).inter measurableSet_Icc
  have hUfin : volume (Set.Icc 0 T) ≠ ⊤ := volume_ne_top_of_subset_Icc subset_rfl
  have hsq := vol_inter_lower (A := Q₁ ∩ Set.Icc 0 T)
    (C := (fun τ : ℝ => a * τ + b) ⁻¹' Q₂ ∩ Set.Icc 0 T) (U := Set.Icc 0 T)
    Set.inter_subset_right Set.inter_subset_right hAm hCm measurableSet_Icc hUfin
  have hvolU : vol (Set.Icc 0 T) = T := by rw [vol_Icc hT.le]; ring
  rw [hvolU] at hsq
  have hset2 : Q₁ ∩ (fun τ : ℝ => a * τ + b) ⁻¹' Q₂ ∩ Set.Icc 0 T
      = (Q₁ ∩ Set.Icc 0 T) ∩ ((fun τ : ℝ => a * τ + b) ⁻¹' Q₂ ∩ Set.Icc 0 T) := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  rw [hset2]
  linarith [hsq, hQ₁, hC]

end Work.EKLC8Core
