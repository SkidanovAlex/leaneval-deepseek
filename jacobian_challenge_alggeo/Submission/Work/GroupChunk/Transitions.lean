/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the transition morphisms `t i j`

Assuming the existence lemma `t_exists` (which constructs the restriction of `σ i j` to the
transition domain), this file fixes the transition morphism

`t i j : Opens.toOver (U i j) ⟶ Opens.toOver (U j i)`

and records its two characterisations: it computes the value of `σ i j` (`t_value`) and it
preserves the divisor class (`t_cls`).
-/
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.t_exists

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

section

variable [D : Input C P0]

/-- The transition morphism `t i j : U i j ⟶ U j i`, the restriction of `σ i j` to the
transition domain. -/
def t (i j : D.Idx) : Opens.toOver (U i j) ⟶ Opens.toOver (U j i) :=
  Classical.choose (t_exists (C := C) (P0 := P0) i j)

/-- The specification of `t i j`. -/
theorem t_spec (i j : D.Idx) :
    (∀ {F : Type u} [Field F] [Algebra K F]
        (p : FPt (Opens.toOver (U i j)) F)
        (hp : RPt.LandsIn (p ≫ Uι i j) (σ i j).domain),
        p ≫ t i j ≫ Uι j i = σVal i j _ hp)
    ∧ (∀ {F : Type u} [Field F] [Algebra K F] (p : FPt (Opens.toOver (U i j)) F),
        D.picOf j (p ≫ t i j ≫ Uι j i) = D.picOf i (p ≫ Uι i j)) :=
  Classical.choose_spec (t_exists (C := C) (P0 := P0) i j)

/-- The transition computes the value of `σ i j`. -/
theorem t_value (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver (U i j)) F)
    (hp : RPt.LandsIn (p ≫ Uι i j) (σ i j).domain) :
    p ≫ t i j ≫ Uι j i = σVal i j _ hp :=
  (t_spec i j).1 p hp

/-- The transition preserves the divisor class. -/
theorem t_cls (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver (U i j)) F) :
    D.picOf j (p ≫ t i j ≫ Uι j i) = D.picOf i (p ≫ Uι i j) :=
  (t_spec i j).2 p

end

end

end Work.GroupChunk
