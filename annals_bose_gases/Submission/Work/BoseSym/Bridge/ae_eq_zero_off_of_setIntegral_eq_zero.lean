import Mathlib.MeasureTheory.Function.AEEqOfIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Bridge

theorem ae_eq_zero_off_of_setIntegral_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] {S : Set α}
    (hS : MeasurableSet S) {f : α → ℝ}
    (hf : ∀ s : Set α, MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn f s μ)
    (h0 : ∀ A : Set α, MeasurableSet A → μ A < ⊤ → A ⊆ Sᶜ → ∫ x in A, f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∉ S → f x = 0 := by
  have h : f =ᵐ[μ.restrict Sᶜ] 0 := by
    refine MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
      (μ := μ.restrict Sᶜ) (f := f) ?_ ?_
    · intro s hs hsfin
      have hμ : μ (s ∩ Sᶜ) < ⊤ := by
        rwa [MeasureTheory.Measure.restrict_apply hs] at hsfin
      rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_restrict hs]
      exact hf (s ∩ Sᶜ) (hs.inter hS.compl) hμ
    · intro s hs hsfin
      have hμ : μ (s ∩ Sᶜ) < ⊤ := by
        rwa [MeasureTheory.Measure.restrict_apply hs] at hsfin
      rw [MeasureTheory.Measure.restrict_restrict hs]
      exact h0 (s ∩ Sᶜ) (hs.inter hS.compl) hμ Set.inter_subset_right
  have h' : ∀ᵐ x ∂(μ.restrict Sᶜ), f x = 0 := h
  rw [MeasureTheory.ae_restrict_iff' hS.compl] at h'
  filter_upwards [h'] with x hx hxS
  exact hx hxS

end Work.BoseSym.Bridge
