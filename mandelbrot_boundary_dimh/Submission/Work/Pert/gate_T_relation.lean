import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

/-- **(A.4.2), the relation between the two gate coordinates.**  If `Tt α` (the deck translation
`w ↦ w - 1/α`) maps the gate `Qreg b₁ b₂` into the gate `Qreg c₁ c₂`, intertwines `F` with itself
(`F ∘ Tt α = Tt α ∘ F`) there, and `Φp`, `Φm` are Fatou coordinates of `F` on the two gates, then
`Φm ∘ Tt α` is *again* a Fatou coordinate of `F` on `Qreg b₁ b₂` (it is differentiable, injective,
and satisfies the Abel equation because `Tt α` commutes with `F`), so the uniqueness of Fatou
coordinates `FatouUnique` forces it to differ from `Φp` by a constant. -/
theorem gate_T_relation {F Φm Φp : ℂ → ℂ} {α : ℂ} {b₁ b₂ c₁ c₂ : Option ℂ}
    (hU : MandelDim.FatouUnique)
    (hadm : MandelDim.QAdm b₁ b₂) (hadm' : MandelDim.QAdm c₁ c₂)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hmaps : ∀ w ∈ MandelDim.Qreg b₁ b₂, Work.Pert.Tt α w ∈ MandelDim.Qreg c₁ c₂)
    (heq : ∀ w ∈ MandelDim.Qreg b₁ b₂, F (Work.Pert.Tt α w) = Work.Pert.Tt α (F w))
    (hΦm : MandelDim.IsFatouCoordOn F Φm (MandelDim.Qreg c₁ c₂))
    (hΦp : MandelDim.IsFatouCoordOn F Φp (MandelDim.Qreg b₁ b₂)) :
    ∃ d : ℂ, ∀ w ∈ MandelDim.Qreg b₁ b₂, Φm (Work.Pert.Tt α w) = Φp w + d := by
  -- the admissibility `hadm'` of the target gate is part of the hypothesis package but is not
  -- needed for the transport itself
  have _ := hadm'
  -- `Φm ∘ Tt α` is a Fatou coordinate of `F` on the gate `Qreg b₁ b₂`
  have hΦ : MandelDim.IsFatouCoordOn F (fun w => Φm (Work.Pert.Tt α w))
      (MandelDim.Qreg b₁ b₂) := by
    refine ⟨?_, ?_, ?_⟩
    · -- differentiability: `Φm` is differentiable on the target gate, `Tt α` is affine
      exact hΦm.1.comp (differentiableOn_id.sub_const ((1 : ℂ) / α)) hmaps
    · -- injectivity: `Φm` is injective on the target gate, `Tt α` is injective
      exact hΦm.2.1.comp (sub_left_injective (b := (1 : ℂ) / α)).injOn hmaps
    · -- Abel equation: `Tt α` commutes with `F`
      intro w hw hFw
      have hTw : Work.Pert.Tt α w ∈ MandelDim.Qreg c₁ c₂ := hmaps w hw
      have hFTw : F (Work.Pert.Tt α w) ∈ MandelDim.Qreg c₁ c₂ := by
        rw [heq w hw]; exact hmaps (F w) hFw
      change Φm (Work.Pert.Tt α (F w)) = Φm (Work.Pert.Tt α w) + 1
      have h := hΦm.2.2 (Work.Pert.Tt α w) hTw hFTw
      rw [← heq w hw]
      exact h
  -- uniqueness of the Fatou coordinate on `Qreg b₁ b₂`
  exact hU b₁ b₂ F Φp (fun w => Φm (Work.Pert.Tt α w)) hadm hNT hΦp hΦ

end Work.Pert
