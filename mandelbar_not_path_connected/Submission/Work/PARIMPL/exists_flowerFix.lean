import Mathlib
import Submission.Work.PARIMPL.Match
import Submission.Work.FatouCoordFix.FlowerFix.ExistsFix
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.FSeed.RootParabolic
import Submission.Work.PARIMPL.flowerFix_of_fatouCoordFix
import Submission.Work.Final.RootArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL

theorem exists_flowerFix {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) : ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁, Nonempty (Work.PARIMPL.FlowerFix d (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁ fl.Pa fl.φa) := by
  obtain ⟨fl⟩ :=
    Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix (Work.PARIMPL.Ft c₀)
      (Work.PARIMPL.gtc c₀) d.z₁
      (Work.Final.differentiable_F c₀)
      (fun z => (Work.Final.differentiable_star_Tantibar_five c₀).differentiableAt)
      (Work.Final.Tantibar_five_comp_self c₀)
      (Work.Final.Tantibar_five_fix d.per_half)
      d.mult d.simple d.per_half
  exact ⟨fl, flowerFix_of_fatouCoordFix d fl⟩

end Work.PARIMPL
