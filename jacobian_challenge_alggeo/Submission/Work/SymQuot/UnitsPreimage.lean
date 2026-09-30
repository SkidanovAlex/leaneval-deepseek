/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The preimage of the units under a monoid homomorphism

An element `m` of a monoid `M` is sent by `φ : M →* N` into the units of `N` exactly when it
belongs to `Submonoid.comap φ (units of N)`.  This is the multiplicative set at which the
localization of a ring along an open immersion of affine schemes takes place.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot

/-- The submonoid of elements of `M` whose image under `φ` is a unit. -/
def unitsPreimage {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N) : Submonoid M where
  carrier := {m | IsUnit (φ m)}
  one_mem' := by simpa using isUnit_one
  mul_mem' := fun ha hb => by simpa using ha.mul hb

@[simp]
lemma mem_unitsPreimage {M N : Type*} [Monoid M] [Monoid N] {φ : M →* N} {m : M} :
    m ∈ unitsPreimage φ ↔ IsUnit (φ m) := Iff.rfl

end Work.SymQuot
