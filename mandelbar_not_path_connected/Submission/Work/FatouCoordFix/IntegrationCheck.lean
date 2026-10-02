/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoordFix team
-/
/-
# Integration check: the repaired flower at the tricorn call site

A *usability* check of the interface of `Submission/Work/FatouCoordFix/` at the call site of the
consumer `Work.Final`: it instantiates
`Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix` (and its `_small` form) at a
root-parabolic parameter `c` — with `F = (T_c)^10`, `g = (T_c)^5`, `z0 = d.z1` — passing exactly
the arguments that the delivered `Work.Final.exists_flower` passes to
`Work.FatouCoord.Flower.exists_parabolicFlower`.

It also checks that the *false* interface hypothesis `Set.MapsTo g Pa Pa` of the delivered area
is not needed any more (`phi_comp_fix` uses the new field `fl.φa_shift`), that the Écalle height
of the critical orbit is independent of the tap time (`critHeight_tap_independent`, without the
`hmaps` input of `Work.Final.RootArc`), and that a `ParabolicFlowerFix` can be passed where a
`ParabolicFlower` is expected (`coe_usable`, via the `Coe` instance).
-/
import Submission.Work.Final.RootArc
import Submission.Work.FatouCoordFix.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

namespace Work.FatouCoordFix.IntegrationCheck

open LeanEval.ComplexAnalysis (Tantibar)

/-- The consumer's call site: the repaired flower exists at a root-parabolic parameter, with the
same arguments as `Work.Final.exists_flower`. -/
theorem exists_flowerFix {c : ℂ} (d : Work.EL.RootParabolic c) :
    Nonempty (Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :=
  Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) d.z₁
    (Work.Final.differentiable_F c)
    (Work.Final.differentiable_star_Tantibar_five c)
    (Work.Final.Tantibar_five_comp_self c)
    (Work.Final.Tantibar_five_fix d.per_half)
    d.mult d.simple d.per_half

/-- The small-petal form: for every `δ > 0` the petal and the half-petal fit in `ball z₁ δ`. -/
theorem exists_flowerFix_small {c : ℂ} (d : Work.EL.RootParabolic c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) d.z₁,
      fl.Pa ⊆ Metric.ball d.z₁ δ ∧ fl.Pg ⊆ Metric.ball d.z₁ δ :=
  Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix_small (Work.EL.F c) ((Tantibar c)^[5])
    d.z₁ (Work.Final.differentiable_F c) (Work.Final.differentiable_star_Tantibar_five c)
    (Work.Final.Tantibar_five_comp_self c) (Work.Final.Tantibar_five_fix d.per_half)
    d.mult d.simple d.per_half hδ

/-- `RootArc.phi_comp` with the interface hypothesis discharged by the new field. -/
theorem phi_comp_fix {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c)
    ((Tantibar c)^[5]) d.z₁) {z : ℂ} (hz : z ∈ fl.Pa) :
    fl.φa (Work.EL.F c z) = fl.φa z + 1 :=
  fl.φa_shift z hz

/-- The Écalle height of the critical orbit does not depend on the tap time, with no extra
hypothesis (`Work.Final.RootArc.critHeight_eq_ecalleHeightAt` minus its `hmaps` input). -/
theorem critHeight_tap_independent {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoordFix.ParabolicFlowerFix
    (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) {n m : ℕ} (hnm : n ≤ m)
    (hmem : (Work.EL.F c)^[n] c ∈ fl.Pa) :
    (fl.φa ((Work.EL.F c)^[m] c)).im = (fl.φa ((Work.EL.F c)^[n] c)).im := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hiter : (Work.EL.F c)^[n + k] c = (Work.EL.F c)^[k] ((Work.EL.F c)^[n] c) := by
    rw [Nat.add_comm n k, Function.iterate_add_apply]
  rw [hiter]
  exact fl.ecalleHeight_iterate hmem k

/-- The `FatouCoordFix` flower is usable as a plain `ParabolicFlower` (`Coe` instance). -/
theorem coe_usable {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoordFix.ParabolicFlowerFix
    (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :
    ((fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)).Pa = fl.Pa := rfl

end Work.FatouCoordFix.IntegrationCheck
