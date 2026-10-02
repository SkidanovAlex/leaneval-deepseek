/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoordFix team
-/
import Mathlib
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.FatouCoordFix.FlowerFix.measurable_indicator_of_differentiableOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The flower restated on the `g`-invariant half-petal `Pg`

`Work.FatouCoordFix.ParabolicFlowerFix` keeps the whole (wide) petal `Pa` of the delivered
`ParabolicFlower` — necessary, because the `cover` field of the interface is about `Pa` — and
adds a *small* `g`-invariant half-petal `Pg ⊆ Pa` together with the Abel equation
`φa ∘ F = φa + 1` on the whole of `Pa`.

The present file packages **the part of the flower that lives on `Pg`** into a structure
`HalfPetalFlower`, i.e. exactly the interface that the consumers (`Work.Final.RootArc`,
`Work.FQC.PetalInput`) need:

* `Pg` is open, nonempty, preconnected, avoids `z₀`, and is invariant under both `F` and `g`;
* every orbit converging to `z₀` without hitting it enters `Pg`;
* `φa` is an antiholomorphic Fatou coordinate on `Pg` (`φa ∘ g = conj ∘ φa + 1/2`, and hence
  `φa ∘ F = φa + 1`), injective and analytic there;
* `φa` is **measurable on `Pg`**: `Measurable (Pg.indicator φa)`.  This is the field that is
  unprovable for the junk extension of `φa` off the petal (the delivery note §3.1: "φa off Pa is
  junk"), and it is the form in which `Work.FQC` should consume measurability.

`ParabolicFlowerFix.toHalfPetalFlower` produces the structure.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoordFix

noncomputable section

variable {F g φa : ℂ → ℂ} {z₀ : ℂ} {Pg : Set ℂ}

/-- **The Leau–Fatou flower of `F` (with antiholomorphic square root `g`) restated on the
`g`-invariant half-petal `Pg`.**  This is the narrow interface the consumers should use; it is
produced from a `ParabolicFlowerFix` by `ParabolicFlowerFix.toHalfPetalFlower`. -/
structure HalfPetalFlower (F g : ℂ → ℂ) (z₀ : ℂ) where
  /-- the `g`-invariant half-plane sub-petal -/
  Pg : Set ℂ
  /-- the antiholomorphic Fatou coordinate -/
  φa : ℂ → ℂ
  isOpen_Pg : IsOpen Pg
  Pg_nonempty : Pg.Nonempty
  isPreconnected_Pg : IsPreconnected Pg
  z₀_not_mem_Pg : z₀ ∉ Pg
  mapsTo_F_Pg : MapsTo F Pg Pg
  mapsTo_g_Pg : MapsTo g Pg Pg
  /-- every orbit converging to `z₀` without hitting it enters `Pg` -/
  tendsto_Pg : ∀ z ∈ Pg, Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₀)
  enters_Pg : ∀ z : ℂ, Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₀) →
    (∀ n : ℕ, F^[n] z ≠ z₀) → ∃ n : ℕ, F^[n] z ∈ Pg
  /-- the antiholomorphic Abel equation, and injectivity, on `Pg` -/
  φa_fatou : Work.FatouCoord.IsAntiholomorphicFatouOn g φa Pg ∧ Set.InjOn φa Pg
  /-- the (holomorphic) Abel equation for the return map `F` on `Pg` -/
  φa_fatou_F : Work.FatouCoord.IsFatouCoordinateOn F φa Pg
  φa_analytic : AnalyticOnNhd ℂ φa Pg
  /-- measurability of `φa` **on `Pg`**, in the indicator form (the junk values of `φa` off
  `Pg` are replaced by `0`) -/
  φa_measurable : Measurable (Pg.indicator φa)

namespace ParabolicFlowerFix

variable (h : ParabolicFlowerFix F g z₀)

/-- **A repaired flower yields the flower restated on its half-petal.** -/
def toHalfPetalFlower : HalfPetalFlower F g z₀ where
  Pg := h.Pg
  φa := h.φa
  isOpen_Pg := h.isOpen_Pg
  Pg_nonempty := h.Pg_nonempty
  isPreconnected_Pg := h.isPreconnected_Pg
  z₀_not_mem_Pg := h.z₀_not_mem_Pg
  mapsTo_F_Pg := h.mapsTo_F_Pg
  mapsTo_g_Pg := h.mapsTo_g_Pg
  tendsto_Pg := fun z hz => h.tendsto_Pg hz
  enters_Pg := h.enters_Pg
  φa_fatou := ⟨h.antiholomorphicFatouOn_Pg, h.injective_φa_Pg⟩
  φa_fatou_F := h.fatouCoordinateOn_Pg
  φa_analytic := h.differentiableOn_φa_Pg.analyticOnNhd h.isOpen_Pg
  φa_measurable :=
    Work.FatouCoordFix.FlowerFix.measurable_indicator_of_differentiableOn
      h.isOpen_Pg h.differentiableOn_φa_Pg

@[simp] theorem toHalfPetalFlower_Pg : h.toHalfPetalFlower.Pg = h.Pg := rfl
@[simp] theorem toHalfPetalFlower_φa : h.toHalfPetalFlower.φa = h.φa := rfl

end ParabolicFlowerFix

/-! ## API of `HalfPetalFlower` -/

namespace HalfPetalFlower

variable (h : HalfPetalFlower F g z₀)

/-- `φa` is holomorphic on `Pg`. -/
theorem differentiableOn_φa : DifferentiableOn ℂ h.φa h.Pg := h.φa_fatou_F.1

/-- Iterating the Abel equation for `F` on `Pg`. -/
theorem φa_iterate {z : ℂ} (hz : z ∈ h.Pg) (k : ℕ) : h.φa ((F^[k]) z) = h.φa z + k :=
  h.φa_fatou_F.iterate h.mapsTo_F_Pg hz k

/-- The Écalle height is invariant under the return map on `Pg`. -/
theorem ecalleHeight_map_F {z : ℂ} (hz : z ∈ h.Pg) :
    (h.φa (F z)).im = (h.φa z).im := by
  rw [h.φa_fatou_F.2 z hz]
  simp

/-- On `Pg` the antiholomorphic relation squares to the Abel equation for `F`. -/
theorem comp_self : Work.FatouCoord.IsFatouCoordinateOn F h.φa h.Pg :=
  h.φa_fatou_F

/-- The equator `Im φa = 0` is invariant under `g` on `Pg`. -/
theorem equator_mapsTo {z : ℂ} (hz : z ∈ Work.FatouCoord.equator h.φa) (hzP : z ∈ h.Pg) :
    g z ∈ Work.FatouCoord.equator h.φa :=
  h.φa_fatou.1.equator_mapsTo hz hzP

/-- The Écalle height changes sign under the antiholomorphic half-return `g`. -/
theorem ecalleHeight_map_g {z : ℂ} (hz : z ∈ h.Pg) :
    Work.FatouCoord.ecalleHeight h.φa (g z) = -Work.FatouCoord.ecalleHeight h.φa z :=
  h.φa_fatou.1.ecalleHeight_map hz

end HalfPetalFlower

end

end Work.FatouCoordFix
