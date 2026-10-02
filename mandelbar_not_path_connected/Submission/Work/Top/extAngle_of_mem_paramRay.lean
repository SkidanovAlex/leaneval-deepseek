import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.extAngle_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- A point of the parameter ray of angle `β` is the point of that ray at some level `t > 1`,
so its external angle is `β`. -/
theorem extAngle_of_mem_paramRay {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {β : ℝ}
    (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) {c : ℂ} (hc : c ∈ Work.Top.NakaneData.paramRay hN β) :
    Work.Top.NakaneData.extAngle Φ c = β := by
  obtain ⟨hcMb, t, ht, htEq⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hc
  have hpt : Work.Top.NakaneData.rayPt hN β t = c :=
    hN.injOn_Phi (hN.rayPt_notMem ht) hcMb (by rw [hN.Phi_rayPt ht, htEq])
  rw [← hpt]
  exact Work.Top.extAngle_rayPt hN hβ₀ hβ₁ ht

end Work.Top
