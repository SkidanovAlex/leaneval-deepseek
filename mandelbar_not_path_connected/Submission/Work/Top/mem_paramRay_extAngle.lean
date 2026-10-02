import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Phi_eq_norm_mul_exp_extAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

theorem mem_paramRay_extAngle {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {c : ℂ}
    (hc : c ∉ Mb) : c ∈ Work.Top.NakaneData.paramRay hN (Work.Top.NakaneData.extAngle Φ c) := by
  refine ⟨hc, ‖Φ c‖, hN.Phi_mem_exteriorDisc hc, ?_⟩
  exact Phi_eq_norm_mul_exp_extAngle hN (hN.Phi_ne_zero hc)

end Work.Top
