/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The order of vanishing of a uniformizer is one

The local ring `O_{C,Q}` of a curve at a place `Q` is a discrete valuation ring, so its
maximal ideal is principal; `Q.uniformizer` is a generator of that maximal ideal, viewed in
the function field `K(C)`.  The order of vanishing of a generator of the maximal ideal at `Q`
is exactly `1`, which is Mathlib's `Scheme.ord`: this is the statement that a uniformizer
vanishes to order one.

The mathematical content is entirely ring-theoretic: in a discrete valuation ring, a
generator of the maximal ideal is irreducible, and the order of an irreducible element of a
discrete valuation ring inside its fraction field is `1`
(Mathlib's `Ring.ordFrac_irreducible`).
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics

/-- In a discrete valuation ring, a generator of the maximal ideal is irreducible, i.e. a
uniformizer. -/
theorem irreducible_generator_maximalIdeal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    Irreducible (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal R)) := by
  have hne : Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal R) ≠ 0 := by
    rw [ne_eq, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
    exact IsDiscreteValuationRing.not_a_field R
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    hne (Submodule.IsPrincipal.span_singleton_generator _).symm

end Work.CurveBasics

namespace Work.CurveBasics.Place

open Work.CurveBasics in
theorem ord_uniformizer {k : Type*} [Field k] {C : Curve k} (Q : C.Place) :
    AlgebraicGeometry.Scheme.ord Q.uniformizer Q.point = 1 := by
  haveI hdvr : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  have hco : Order.coheight Q.point = 1 := Q.eq_coheight_one
  -- `Q.uniformizer` is the image of a generator of the maximal ideal in the function field
  rw [show Q.uniformizer = algebraMap (C.left.presheaf.stalk Q.point) C.functionField
      (Submodule.IsPrincipal.generator
        (IsLocalRing.maximalIdeal (C.left.presheaf.stalk Q.point))) from rfl]
  -- the order of vanishing of `f` at a point of codimension one is `ordFrac` of its germ
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hco]
  rw [show Scheme.ordHom Q.point hco =
      Ring.ordFrac (C.left.presheaf.stalk Q.point) from rfl]
  -- a generator of the maximal ideal is a uniformizer, hence has order one
  rw [Ring.ordFrac_irreducible irreducible_generator_maximalIdeal]
  simp [WithZero.exp]

end Work.CurveBasics.Place
