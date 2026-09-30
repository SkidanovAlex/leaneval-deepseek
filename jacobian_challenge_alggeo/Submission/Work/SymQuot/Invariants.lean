/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariant rings (area SY)

Ring-theoretic facts about the ring of invariants `B^G` of a finite group `G` acting on a
commutative ring `B`, which underlie the construction of the quotient `X/G` of a scheme by a
finite group.

The main results (proved in the companion files of this directory) are:

* `Work.SymQuot.fixedPoints_isInvariant`: `B^G ⊆ B` is an invariant extension.
* `Work.SymQuot.fixedPoints_lift`: the universal property of `B^G` among `G`-invariant ring
  maps out of `B`.
* `Work.SymQuot.fixedPoints_isLocalization_away`: localizing `B` at a `G`-invariant element
  commutes with passing to invariants.
* `Work.SymQuot.fixedPoints_flatBaseChange`: invariants commute with flat base change.
* `Work.SymQuot.fixedPoints_isIntegral`: `B` is integral over `B^G`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory

universe u v w

namespace Work.SymQuot

section Ring

variable {G : Type u} [Group G] {A : Type v} [CommRing A] [MulSemiringAction G A]
  {B : Type w} [CommRing B] [MulSemiringAction G B] [Algebra A B]

/-- The ring homomorphism `A^G →+* B^G` induced by a `G`-equivariant ring homomorphism
`A →+* B` (here `B` is an `A`-algebra). -/
def fixedPointsMap (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a) :
    FixedPoints.subring A G →+* FixedPoints.subring B G where
  toFun a := ⟨algebraMap A B a.1, fun g => by
    rw [← hcompat g a.1, a.2 g]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma fixedPointsMap_coe
    (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (a : FixedPoints.subring A G) :
    ((fixedPointsMap hcompat a : FixedPoints.subring B G) : B) = algebraMap A B (a : A) := rfl

/-- Membership in the fixed points. -/
lemma mem_fixedPoints_iff {b : B} :
    b ∈ FixedPoints.subring B G ↔ ∀ g : G, g • b = b :=
  FixedPoints.mem_submonoid G B b

@[simp]
lemma mem_fixedPoints {b : B} :
    b ∈ FixedPoints.subring B G ↔ ∀ g : G, g • b = b :=
  mem_fixedPoints_iff

end Ring

end Work.SymQuot
