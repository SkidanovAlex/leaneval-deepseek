import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

theorem arms_basic {c : ℂ} (S : Work.ELNest.NestData c) :
    IsOpen S.armA ∧ IsOpen S.armB ∧ IsOpen S.armC ∧
    Disjoint S.armA S.armB ∧ Disjoint S.armB S.armC ∧ Disjoint S.armC S.armA ∧
    S.armA ∪ S.armB ∪ S.armC = (Work.EL.Tripod.curve S.tripod)ᶜ := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  obtain ⟨hdisjAB, hdisjBC, hdisjCA⟩ :=
    Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod
  have hcov := Work.ELTop.tripodArms_cover S.d.hN hJ S.tripod
  refine ⟨?_, ?_, ?_, hdisjAB, hdisjBC, hdisjCA, hcov⟩
  · exact (Work.ELTop.isOpen_pairSide S.d.hN (S.tripod.pairA)).1
  · exact (Work.ELTop.isOpen_pairSide S.d.hN (S.tripod.pairB)).1
  · exact (Work.ELTop.isOpen_pairSide S.d.hN (S.tripod.pairC)).1

end Work.ELNest
