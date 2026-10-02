import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

namespace Work.Top

/-- The parameter ray of angle `θ` is the image of the interval `(1,∞)` under the level
parametrization `t ↦ rayPt hN θ t`. -/
theorem paramRay_eq_image_rayPt {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ) :
    Work.Top.NakaneData.paramRay hN θ =
      (fun t : ℝ => Work.Top.NakaneData.rayPt hN θ t) '' Set.Ioi 1 := by
  ext c
  rw [Work.Top.NakaneData.mem_paramRay_iff]
  constructor
  · rintro ⟨hc, t, ht, hΦ⟩
    refine ⟨t, ht, ?_⟩
    exact hN.injOn_Phi (hN.rayPt_notMem ht) hc (by rw [hN.Phi_rayPt ht, hΦ])
  · rintro ⟨t, ht, rfl⟩
    exact ⟨hN.rayPt_notMem ht, t, ht, hN.Phi_rayPt ht⟩

/-- A parameter ray is the continuous image of the preconnected interval `(1,∞)`, hence
preconnected. -/
theorem isPreconnected_paramRay {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ) :
    IsPreconnected (Work.Top.NakaneData.paramRay hN θ) := by
  rw [paramRay_eq_image_rayPt hN θ]
  exact isPreconnected_Ioi.image (fun t : ℝ => Work.Top.NakaneData.rayPt hN θ t)
    (Work.Top.continuousOn_rayPt hN θ)

end Work.Top
