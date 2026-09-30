import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot.Invariants

/-- An element of `B` fixed by every element of `G` lies in the fixed subring `B^G`; hence `B`
is an invariant extension of `B^G` (in the sense of `Algebra.IsInvariant`). -/
instance instIsInvariantFixedPointsSubring {G : Type*} [Group G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] : Algebra.IsInvariant (FixedPoints.subring B G) B G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- If a finite group `G` acts on a commutative ring `B` by ring automorphisms, then `B` is
integral over its subring `B^G` of fixed points. Indeed, every `b : B` is a root of the monic
polynomial `∏_{g ∈ G} (X - g • b)`, whose coefficients are fixed by `G`. -/
theorem fixedPoints_isIntegral {G : Type*} [Group G] [Finite G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] : Algebra.IsIntegral (FixedPoints.subring B G) B :=
  Algebra.IsInvariant.isIntegral (FixedPoints.subring B G) B G

end Work.SymQuot.Invariants
