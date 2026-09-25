import Mathlib

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal

theorem translateAverage_integrable {φ : ℝ → ℝ} (hφ : Measurable φ) {g : ℝ → ℂ} (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (fun x : ℝ => ∫ t in (0:ℝ)..1, g (x - φ t)) ∧
    (∫⁻ x : ℝ, ‖(∫ t in (0:ℝ)..1, g (x - φ t))‖ₑ ≤ ∫⁻ x : ℝ, ‖g x‖ₑ) := by
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hν
  set F : ℝ × ℝ → ℂ := fun p => g (p.1 - φ p.2) with hF
  have hΦ_meas : Measurable (fun p : ℝ × ℝ => p.1 - φ p.2) :=
    measurable_fst.sub (hφ.comp measurable_snd)
  -- Absolute continuity of the pushforward of `volume ⊗ ν` under `(x,t) ↦ x - φ t`.
  have hac : Measure.map (fun p : ℝ × ℝ => p.1 - φ p.2) (volume.prod ν) ≪ (volume : Measure ℝ) := by
    have hΨ_meas : Measurable (Prod.map (id : ℝ → ℝ) φ) := measurable_id.prodMap hφ
    have hmap1 : Measure.map (Prod.map (id : ℝ → ℝ) φ) (volume.prod ν)
        = volume.prod (Measure.map φ ν) := by
      have h := Measure.map_prod_map (volume : Measure ℝ) ν measurable_id hφ
      rw [Measure.map_id] at h
      exact h.symm
    have hqmp : Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - p.2)
        (volume.prod (Measure.map φ ν)) volume :=
      quasiMeasurePreserving_sub_of_right_invariant (volume : Measure ℝ) _
    have hΦ_eq : Measure.map (fun p : ℝ × ℝ => p.1 - φ p.2) (volume.prod ν)
        = Measure.map (fun p : ℝ × ℝ => p.1 - p.2) (volume.prod (Measure.map φ ν)) := by
      rw [← hmap1, Measure.map_map]
      · rfl
      · fun_prop
      · exact hΨ_meas
    rw [hΦ_eq]
    exact hqmp.absolutelyContinuous
  have hF_meas : AEStronglyMeasurable F (volume.prod ν) := by
    have h1 : AEStronglyMeasurable g
        (Measure.map (fun p : ℝ × ℝ => p.1 - φ p.2) (volume.prod ν)) :=
      hg.aestronglyMeasurable.mono_ac hac
    exact h1.comp_measurable hΦ_meas
  have hνuniv : ν Set.univ = 1 := by
    rw [hν, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  -- Tonelli: swap the two integrals of the joint `enorm`.
  have hswap : ∫⁻ x : ℝ, ∫⁻ t : ℝ, ‖F (x, t)‖ₑ ∂ν ∂(volume : Measure ℝ)
      = ∫⁻ t : ℝ, ∫⁻ x : ℝ, ‖F (x, t)‖ₑ ∂(volume : Measure ℝ) ∂ν :=
    lintegral_lintegral_swap (f := fun x t => ‖F (x, t)‖ₑ) (hF_meas.enorm)
  have hinner : ∀ t : ℝ, ∫⁻ x : ℝ, ‖F (x, t)‖ₑ ∂(volume : Measure ℝ) = ∫⁻ x : ℝ, ‖g x‖ₑ := by
    intro t
    have h := lintegral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ => ‖g y‖ₑ) (φ t)
    simpa [hF] using h
  have hmain : ∫⁻ x : ℝ, ∫⁻ t : ℝ, ‖F (x, t)‖ₑ ∂ν ∂(volume : Measure ℝ) = ∫⁻ x : ℝ, ‖g x‖ₑ := by
    rw [hswap]
    simp only [hinner]
    rw [lintegral_const, hνuniv, mul_one]
  have hprod : ∫⁻ z : ℝ × ℝ, ‖F z‖ₑ ∂(volume.prod ν) = ∫⁻ x : ℝ, ‖g x‖ₑ := by
    rw [lintegral_prod (fun z : ℝ × ℝ => ‖F z‖ₑ) hF_meas.enorm]
    exact hmain
  have hF_fin : HasFiniteIntegral F (volume.prod ν) := by
    rw [hasFiniteIntegral_iff_enorm, hprod]
    exact hg.hasFiniteIntegral
  have hF_int : Integrable F (volume.prod ν) := ⟨hF_meas, hF_fin⟩
  have hbound : ∫⁻ x : ℝ, ‖∫ t : ℝ, F (x, t) ∂ν‖ₑ ≤ ∫⁻ x : ℝ, ‖g x‖ₑ := by
    calc ∫⁻ x : ℝ, ‖∫ t : ℝ, F (x, t) ∂ν‖ₑ
        ≤ ∫⁻ x : ℝ, ∫⁻ t : ℝ, ‖F (x, t)‖ₑ ∂ν ∂(volume : Measure ℝ) :=
          lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ x : ℝ, ‖g x‖ₑ := hmain
  have hcongr : ∀ x : ℝ, (∫ t in (0:ℝ)..1, g (x - φ t)) = ∫ t : ℝ, F (x, t) ∂ν := by
    intro x
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine ⟨?_, ?_⟩
  · simpa only [hcongr] using hF_int.integral_prod_left
  · simpa only [hcongr] using hbound

end Work.BourgainPlan.Maximal
