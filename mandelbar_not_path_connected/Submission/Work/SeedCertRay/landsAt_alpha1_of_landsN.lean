import Mathlib
import Submission.Work.SeedCertRay.Basic
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- The landing of the ray of angle `α₁` in `Work.Top`'s parametrised vocabulary
(`Work.EL.LandsN`, the convergence of the ray points `t ↦ rayPt hN α₁ t` as `t → 1⁺`)
implies landing in `Work.Landing`'s accumulation-set vocabulary (`Work.Landing.landsAt`).

This is the bridge `Work.ELTop.landsN_iff_landsAt`, specialised at the angle `α₁`. -/
theorem landsAt_alpha1_of_landsN {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) {z₁ : ℂ} (h : Work.EL.LandsN hN Work.EL.alpha1 z₁) : Work.Landing.landsAt c Work.EL.alpha1 z₁ :=
  (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha1 z₁).mp h

end Work.SeedCertRay
