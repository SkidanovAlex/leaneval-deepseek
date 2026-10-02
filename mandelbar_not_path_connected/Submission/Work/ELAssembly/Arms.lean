/-
# `ELAssembly` — the arm bridging between `ELNest`'s tripod and `ELRig`'s `armOf`

`Work.ELNest.NestData` carries its tripod as `Work.EL.Tripod S.d.hN` (`S.tripod`, with the arms
`S.armA`, `S.armB`, `S.armC`), while the consumer `Work.EL.B2Data` records the tripod as the
*structure* `Work.EL.TripodSides hN b₂` and its arms as `Work.EL.armOf T Z`
(`Work.EL.armA hN y T.lands_a T.lands_b` etc.).  The two spellings of the same arm are
definitionally equal (`Work.ELTop.armA_eq`, `..._B_eq`, `..._C_eq`), because the arm only depends
on the landing point `y` of the tripod and never on the proof components of the pair.

This file records the three equalities in the form in which the assembly uses them.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.RigTripod
import Submission.Work.ELRig.Inputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

variable {c : ℂ}

/-- The tripod `Work.EL.Tripod` underlying an `ELNest` tripod is the one built from its fields. -/
theorem tripod_eq {c : ℂ} (S : Work.ELNest.NestData c) :
    (⟨S.b2, S.b2_lands.1, S.b2_lands.2.1, S.b2_lands.2.2, S.b2_lands'⟩ : Work.EL.Tripod S.d.hN)
      = S.tripod := by
  unfold Work.ELNest.NestData.tripod
  rfl

/-- **The arm `A`.**  `Work.EL.armA` of the tripod of `NestData` is `S.armA`. -/
theorem armA_eq (S : Work.ELNest.NestData c) :
    Work.EL.armA S.d.hN S.b2 S.b2_lands.1 S.b2_lands.2.1 = S.armA := by
  rw [Work.ELTop.armA_eq S.d.hN S.b2_lands.1 S.b2_lands.2.1 S.b2_lands.2.2 S.b2_lands']
  unfold Work.ELNest.NestData.armA Work.ELNest.NestData.tripod
  rfl

/-- **The arm `B`.** -/
theorem armB_eq (S : Work.ELNest.NestData c) :
    Work.EL.armB S.d.hN S.b2 S.b2_lands.2.1 S.b2_lands.2.2 = S.armB := by
  rw [Work.ELTop.armB_eq S.d.hN S.b2_lands.1 S.b2_lands.2.1 S.b2_lands.2.2 S.b2_lands']
  unfold Work.ELNest.NestData.armB Work.ELNest.NestData.tripod
  rfl

/-- **The arm `C`.** -/
theorem armC_eq (S : Work.ELNest.NestData c) :
    Work.EL.armC S.d.hN S.b2 S.b2_lands.2.2 S.b2_lands' = S.armC := by
  rw [Work.ELTop.armC_eq S.d.hN S.b2_lands.1 S.b2_lands.2.1 S.b2_lands.2.2 S.b2_lands']
  unfold Work.ELNest.NestData.armC Work.ELNest.NestData.tripod
  rfl

/-- The tripod of `Work.ELTop.tripodSides` has the arms of the `NestData`. -/
theorem armOf_tripodSides_A (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm) :
    Work.EL.armOf (Work.ELTop.tripodSides S.d.hN hJ S.b2_lands.1 S.b2_lands.2.1
      S.b2_lands.2.2 S.b2_lands') Work.EL.ArmIdx.A = S.armA := by
  show Work.EL.armA S.d.hN S.b2 _ _ = S.armA
  exact armA_eq S

theorem armOf_tripodSides_B (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm) :
    Work.EL.armOf (Work.ELTop.tripodSides S.d.hN hJ S.b2_lands.1 S.b2_lands.2.1
      S.b2_lands.2.2 S.b2_lands') Work.EL.ArmIdx.B = S.armB := by
  show Work.EL.armB S.d.hN S.b2 _ _ = S.armB
  exact armB_eq S

theorem armOf_tripodSides_C (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm) :
    Work.EL.armOf (Work.ELTop.tripodSides S.d.hN hJ S.b2_lands.1 S.b2_lands.2.1
      S.b2_lands.2.2 S.b2_lands') Work.EL.ArmIdx.C = S.armC := by
  show Work.EL.armC S.d.hN S.b2 _ _ = S.armC
  exact armC_eq S

end Work.ELAssembly
