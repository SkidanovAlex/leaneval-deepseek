/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area NM — normality of the curve powers and of `Sym^n`

This is the base file of the area: it fixes the single scheme-theoretic notion that the rest of
the area (and its consumers, in particular the `DM`/`DOM` engine) speaks about, namely that a
scheme has *integrally closed local rings* (equivalently: all its stalks are integrally closed,
or: every affine open subscheme has an integrally closed coordinate ring).

## Main definitions

* `Work.Normality.HasIntegrallyClosedStalks X`: every stalk of `X` is an integrally closed ring.

## Main results (in the sibling files)

* `Work.Normality.isIntegrallyClosed_of_smooth`: a domain which is standard smooth of relative
  dimension `n` over a field is integrally closed.
* `Work.Normality.hasIntegrallyClosedStalks_of_smooth`: a smooth, integral scheme over a field
  has integrally closed stalks.
* `Work.Normality.isIntegrallyClosed_invariants`: the fixed points of a finite group acting on
  an integrally closed domain form an integrally closed ring.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Work.Normality

/-- A scheme has *integrally closed stalks* if every one of its local rings is an integrally
closed ring.  For an integral scheme this is the usual notion of a *normal* scheme; we phrase it
on stalks because this is exactly the form in which the `DM` engine consumes it. -/
def HasIntegrallyClosedStalks (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

theorem hasIntegrallyClosedStalks_iff {X : Scheme.{u}} :
    HasIntegrallyClosedStalks X ↔ ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
  Iff.rfl

end Work.Normality
