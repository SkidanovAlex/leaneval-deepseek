import Mathlib
import Submission.Work.FQC.transfer_rays
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- **Transfer of the "no other angles land at `z₁`" statement across the deformation `θ`.**

`Work.ELTop.landsN_iff_landsAt` identifies `Work.EL.LandsN hN₂ ϑ z₁₂` with
`Work.Landing.landsAt c₂ ϑ z₁₂`, and `Work.FQC.transfer_rays` carries the landing statement at
`c₂` back to the landing statement at `c` along `θ`: `landsAt c ϑ z ↔ landsAt c₂ ϑ (θ z)`.
Composing with the hypothesis `hz₁ : z₁₂ = θ z₁` and the angle portrait `hportrait` at `c`
gives the claimed portrait at `c₂`. -/
theorem hzero_of_transfer {c c₂ : ℂ} {φ ψ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ) (hb : Work.ParamRays.IsDynBottcher c φ) (hb₂ : Work.ParamRays.IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ))) (hesc : ∀ z : ℂ, Work.ParamRays.Escaping c₂ (θ z) ↔ Work.ParamRays.Escaping c z) (hN₂ : Work.EL.DynB c₂ ψ) (hψ : Work.ParamRays.IsDynBottcher c₂ ψ) {z₁ z₁₂ : ℂ} (hz₁ : z₁₂ = θ z₁) (hportrait : ∀ ϑ : ℝ, ϑ ∈ Set.Ico 0 1 → (Work.Landing.landsAt c ϑ z₁ ↔ ϑ = Work.EL.alpha1 ∨ ϑ = Work.EL.alpha2)) : ∀ ϑ : ℝ, ϑ ∈ Set.Ico 0 1 → (Work.EL.LandsN hN₂ ϑ z₁₂ ↔ ϑ = Work.EL.alpha1 ∨ ϑ = Work.EL.alpha2) := by
  intro ϑ hϑ
  rw [Work.ELTop.landsN_iff_landsAt hN₂ hψ ϑ z₁₂, hz₁]
  exact ((Work.FQC.transfer_rays θ hb hb₂ hesc ϑ).2 z₁).symm.trans (hportrait ϑ hϑ)

end Work.ELAssembly
