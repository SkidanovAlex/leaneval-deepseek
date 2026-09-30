/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the universal property of the gluing, as a morphism

The existence lemma `Desc.desc_exists` gives the universal property of `GSch D` as an `∃!`.
This file extracts the morphism itself (`desc`) together with its two defining properties,
in the form in which areas UP and DS consume it.
-/
import Submission.Work.GroupChunk.Desc.desc_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-- `desc`: a family of chart maps out of `V` which agrees on the transition domains glues to
a morphism out of `GSch D`. -/
def desc (D : Input C P0) {Y : Sch K} (φ : ∀ i : D.Idx, Opens.toOver D.V ⟶ Y)
    (hφ : ∀ i j : D.Idx, Opens.ιOver (U (D := D) i j) ≫ φ i =
      (t (D := D) i j ≫ Opens.ιOver (U (D := D) j i)) ≫ φ j) : GSch D ⟶ Y :=
  Classical.choose (Desc.desc_exists (D := D) φ hφ)

/-- `desc` restricts to the given chart maps. -/
theorem desc_chart (D : Input C P0) {Y : Sch K} (φ : ∀ i : D.Idx, Opens.toOver D.V ⟶ Y)
    (hφ : ∀ i j : D.Idx, Opens.ιOver (U (D := D) i j) ≫ φ i =
      (t (D := D) i j ≫ Opens.ιOver (U (D := D) j i)) ≫ φ j) (i : D.Idx) :
    chartH D i ≫ desc D φ hφ = φ i :=
  (Classical.choose_spec (Desc.desc_exists (D := D) φ hφ)).1 i

/-- `desc` is the unique morphism with this property. -/
theorem desc_unique (D : Input C P0) {Y : Sch K} (φ : ∀ i : D.Idx, Opens.toOver D.V ⟶ Y)
    (hφ : ∀ i j : D.Idx, Opens.ιOver (U (D := D) i j) ≫ φ i =
      (t (D := D) i j ≫ Opens.ιOver (U (D := D) j i)) ≫ φ j)
    {g : GSch D ⟶ Y} (hg : ∀ i : D.Idx, chartH D i ≫ g = φ i) :
    g = desc D φ hφ :=
  (Classical.choose_spec (Desc.desc_exists (D := D) φ hφ)).2 g hg

end

end Work.GroupChunk
