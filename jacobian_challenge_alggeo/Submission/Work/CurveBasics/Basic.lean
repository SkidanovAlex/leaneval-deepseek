/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Curve basics (area CB)

This file sets up the basic API for a smooth, proper, geometrically irreducible curve
over a field, the ambient object of the Jacobian challenge.

## Main definitions

* `Work.CurveBasics.Curve k`: the bundled notion of a smooth, proper, geometrically
  irreducible curve over a field `k`.
* `Work.CurveBasics.Curve.Place`: the type of closed points of a curve.
* `Work.CurveBasics.Curve.functionField`: the function field `K(C)`.

## Implementation notes

Two facts that are true for a smooth, proper, geometrically irreducible curve over a
field are not yet available in Mathlib and are therefore carried as fields of the
structure (see also the module `Work.CurveBasics.Gaps`):

* `GeometricallyReduced`: a smooth scheme over a field is geometrically reduced;
* `Ring.KrullDimLE 1 (stalk z)`: a scheme smooth of relative dimension `1` over a field
  has local rings of Krull dimension `≤ 1`.

Every other property of a curve used below is *derived* from these.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

/-- A smooth, proper, geometrically irreducible curve over a field `k`.

The fields `geomReduced` and `krullDim_stalk_le_one` are consequences of the
other three hypotheses that are not yet in Mathlib; they are bundled here so that the
rest of the theory can be developed without them, and can be removed once
`Curve.geometricallyReduced_of_smooth` and `Curve.krullDim_le_one_of_smooth`
(see `Work.CurveBasics.Gaps`) are available. -/
structure Curve (k : Type u) [Field k] where
  /-- The underlying `k`-scheme. -/
  toOver : Over (Spec (CommRingCat.of k))
  /-- `C` is smooth of relative dimension `1` over `k`. -/
  smooth : SmoothOfRelativeDimension 1 toOver.hom
  /-- `C` is proper over `k`. -/
  proper : IsProper toOver.hom
  /-- `C` is geometrically irreducible over `k`. -/
  geomIrred : GeometricallyIrreducible toOver.hom
  /-- `C` is geometrically reduced over `k`. -/
  geomReduced : GeometricallyReduced toOver.hom
  /-- The local rings of `C` have Krull dimension at most `1`. -/
  krullDim_stalk_le_one : ∀ z : toOver.left, Ring.KrullDimLE 1 (toOver.left.presheaf.stalk z)
  /-- A curve has more than one point.  This is a consequence of smoothness of relative
  dimension `1` (which forces infinitely many points), bundled for the same reason as the
  two fields above. -/
  nontrivial : Nontrivial toOver.left

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The underlying scheme of a curve. -/
abbrev left (C : Curve k) : Scheme.{u} := C.toOver.left

/-- The structure morphism `C ⟶ Spec k`. -/
abbrev hom (C : Curve k) : C.left ⟶ Spec (CommRingCat.of k) := C.toOver.hom

instance instSmoothOfRelativeDimension (C : Curve k) :
    SmoothOfRelativeDimension 1 C.hom := C.smooth
instance instIsProper (C : Curve k) : IsProper C.hom := C.proper
instance instGeometricallyIrreducible (C : Curve k) :
    GeometricallyIrreducible C.hom := C.geomIrred
instance instGeometricallyReduced (C : Curve k) : GeometricallyReduced C.hom :=
  C.geomReduced

instance (C : Curve k) : GeometricallyIntegral C.hom :=
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom

/-- A curve is integral. -/
instance instIsIntegral (C : Curve k) : IsIntegral C.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton C.hom

instance (C : Curve k) : Nonempty C.left := inferInstance

instance (C : Curve k) : Nontrivial C.left := C.nontrivial

instance (C : Curve k) : IrreducibleSpace C.left := inferInstance

instance (C : Curve k) : IsReduced C.left := inferInstance

instance (C : Curve k) : LocallyOfFiniteType C.hom := inferInstance

/-- A curve is locally noetherian. -/
instance (C : Curve k) : IsLocallyNoetherian C.left :=
  LocallyOfFiniteType.isLocallyNoetherian C.hom

instance (C : Curve k) : IsSeparated C.hom := inferInstance

instance (C : Curve k) : QuasiCompact C.hom := inferInstance

instance (C : Curve k) : CompactSpace C.left :=
  (quasiCompact_iff_compactSpace C.hom).mp inferInstance

/-- A curve is noetherian. -/
instance (C : Curve k) : IsNoetherian C.left := ⟨⟩

instance (C : Curve k) : JacobsonSpace C.left :=
  LocallyOfFiniteType.jacobsonSpace C.hom

/-- The function field `K(C)` of a curve. -/
abbrev functionField (C : Curve k) : CommRingCat.{u} := C.left.functionField

/-- The canonical map from the structure sheaf on an open set to the function field. -/
abbrev germToFunctionField (C : Curve k) (U : C.left.Opens) [Nonempty U] :
    Γ(C.left, U) ⟶ C.functionField := C.left.germToFunctionField U

/-- The structure morphism makes the function field of a curve into a `k`-algebra. -/
instance instAlgebraFunctionField (C : Curve k) : Algebra k C.functionField :=
  haveI : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop ≫
    C.left.germToFunctionField ⊤).hom.toAlgebra

/-- Build a `Curve k` from the hypotheses used in the Jacobian challenge, together with the
two facts that are true for a curve but missing from Mathlib at this pin (see the module
docstring of `Work.CurveBasics.Basic`). -/
def ofOver (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z))
    (hnt : Nontrivial C.left) : Curve k where
  toOver := C
  smooth := ‹SmoothOfRelativeDimension 1 C.hom›
  proper := ‹IsProper C.hom›
  geomIrred := ‹GeometricallyIrreducible C.hom›
  geomReduced := hred
  krullDim_stalk_le_one := hdim
  nontrivial := hnt

end

end Curve

end Work.CurveBasics
