import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.rep_unique_backward
import Submission.Work.FlowerGlue2.repNorm_comp_add
import Submission.Work.FlowerGlue2.repNorm_congr_left
import Submission.Work.PARIMPL2.Lavaurs.RepNorm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

/-- **`RepNorm` transfers from a reference repelling coordinate to the flower's own repelling
coordinate.**

Both coordinates are repelling coordinates of the same parabolic germ: `Ψ₁` is a reference
repelling coordinate (`IsRepellingCoord`) which surjects onto a Stolz petal `Dst P R₂` from the
far-left half-plane, and `fl.Ψ` is the flower's repelling coordinate.  By the unconditional
repelling Fatou uniqueness `rep_unique_backward` the two differ by a translation on a far-left
half-plane, `fl.Ψ u = Ψ₁ (u + s)` for `Re u < -N`.  But `RepNorm` only ever inspects the
coordinate on a far-left half-plane (`{Re u < -R/2}` for large `R`), so this agreement suffices:

* `repNorm_comp_add` moves the normalisation of `Ψ₁` to its translate `u ↦ Ψ₁ (u + s)`;
* `repNorm_congr_left` transfers it along the half-plane agreement to `fl.Ψ`. -/
theorem repNorm_of_flower {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    {R₁ : ℝ} {Ψ₁ : ℂ → ℂ}
    (h₁ : Work.FatouCoord.IsRepellingCoord (Work.PARIMPL.Ft c₀) d.z₁ R₁ Ψ₁)
    (hsurj : ∃ R₂ : ℝ, ∀ z ∈ Work.FlowerGlue2.Dst P R₂,
      ∃ w' : ℂ, w'.re < -R₁ - 2 ∧ Ψ₁ w' = z)
    (hrn₁ : Work.PARIMPL2.Lavaurs.RepNorm P Ψ₁) :
    Work.PARIMPL2.Lavaurs.RepNorm P fl.Ψ := by
  obtain ⟨s, N, hN⟩ := rep_unique_backward P hτ fl.toParabolicFlower h₁ hsurj
  exact repNorm_congr_left P N hN (repNorm_comp_add P hrn₁ s)

end Work.FlowerGlue2
