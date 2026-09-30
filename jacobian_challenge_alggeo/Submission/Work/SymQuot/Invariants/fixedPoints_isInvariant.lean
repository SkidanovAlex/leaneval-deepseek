import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot.Invariants

/-- Every element of `B` that is fixed by every element of `G` already lies in the fixed subring
`B^G`, i.e. in the image of the structure map `B^G → B`.  Equivalently, `B` is an invariant
extension of `B^G` in the sense of `Algebra.IsInvariant`. -/
theorem fixedPoints_isInvariant {G : Type*} [Group G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] : Algebra.IsInvariant (FixedPoints.subring B G) B G :=
  ⟨fun _ hb => ⟨⟨_, hb⟩, rfl⟩⟩

end Work.SymQuot.Invariants
