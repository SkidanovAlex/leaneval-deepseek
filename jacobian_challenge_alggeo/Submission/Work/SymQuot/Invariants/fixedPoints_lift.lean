import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot.Invariants

theorem fixedPoints_lift {G : Type*} [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B]
    {R : Type*} [CommRing R] (f : R →+* B) (hf : ∀ (g : G) (r : R), g • f r = f r) :
    ∃! F : R →+* FixedPoints.subring B G, ∀ r : R, (F r : B) = f r := by
  let F : R →+* FixedPoints.subring B G :=
    { toFun := fun r => ⟨f r, fun g => hf g r⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun a b => Subtype.ext (f.map_mul a b)
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun a b => Subtype.ext (f.map_add a b) }
  have hF : ∀ r : R, (F r : B) = f r := fun r => rfl
  refine ⟨F, hF, ?_⟩
  rintro F' hF'
  ext r
  rw [hF' r, hF r]

end Work.SymQuot.Invariants
