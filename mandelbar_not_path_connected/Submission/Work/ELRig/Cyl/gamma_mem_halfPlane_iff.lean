import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.TailBand

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig.Cyl

open Classical Set

/-- **`γ₁` lies in the half plane `{Re < -L.R}` exactly when its `Ψ`-image (the point
`rayPt α₁ (L.τ s)` of the root ray) has a `Ψ`-preimage in that half plane**, and in that case
`γ₁ s` *is* the chosen inverse image `invFunOn fl.Ψ {Re < -L.R}`.

The content is `RayCylLift.tailId₁` (in the far-left half plane the `Ψ`-preimages of the
`α₁`-ray are exactly the lift `γ₁`), the injectivity of the level map of a ray point
(`Work.ELRig.rayPt_level_inj`), and `RayCylLift.hinj` (injectivity of `fl.Ψ` on the half
plane). -/
theorem gamma_mem_halfPlane_iff {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    ((L.γ₁ s).re < -L.R ↔
      Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s) ∈ fl.Ψ '' {w : ℂ | w.re < -L.R}) ∧
    ((L.γ₁ s).re < -L.R →
      L.γ₁ s = Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s))) := by
  constructor
  · constructor
    · intro h
      exact ⟨L.γ₁ s, h, (L.hΨ₁ s)⟩
    · rintro ⟨w, hw, hwΨ⟩
      have hmem : w ∈ Set.range L.γ₁ :=
        L.tailId₁ w hw (by rw [hwΨ]; exact Work.EL.rayPt_mem_paramRay d.hN (L.hτ1 s))
      obtain ⟨s', rfl⟩ := hmem
      have hΨeq : Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s')
          = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s) := by
        rw [← L.hΨ₁ s', hwΨ]
      have hsl : s' = s :=
        L.hτmono.injective
          (Work.ELRig.rayPt_level_inj d.hN (L.hτ1 s') (L.hτ1 s) hΨeq)
      rwa [hsl] at hw
  · intro h
    have hwit : ∃ w ∈ {w : ℂ | w.re < -L.R},
        fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s) :=
      ⟨L.γ₁ s, h, L.hΨ₁ s⟩
    have hmem := Function.invFunOn_mem hwit
    have heq := Function.invFunOn_eq hwit
    exact L.hinj h hmem (by rw [L.hΨ₁ s, heq])

end Work.ELRig.Cyl
