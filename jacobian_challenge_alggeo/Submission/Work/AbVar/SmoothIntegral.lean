/-
Area AV (abelian-variety toolkit) for the Jacobian challenge:
smooth + geometrically irreducible ⇒ geometrically integral, and consequences.
-/
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.SmoothReduced.geometricallyIntegral_of_smooth_of_geometricallyIrreducible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Abelian varieties are geometrically integral (and commutative)

Over a field, a smooth scheme is geometrically reduced, hence smooth + geometrically
irreducible schemes are geometrically integral. Applied to an abelian variety (smooth,
proper, geometrically irreducible) this gives geometric integrality and, via
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, commutativity
of the group law.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj
open AlgebraicGeometry

namespace Work.AbVar

variable {k : Type u} [Field k]

/-- Over a field, a smooth and geometrically irreducible scheme is geometrically integral. -/
theorem geometricallyIntegral_of_smooth_of_geometricallyIrreducible' (X : Sch k)
    [Smooth X.hom] [GeometricallyIrreducible X.hom] : GeometricallyIntegral X.hom :=
  SmoothReduced.geometricallyIntegral_of_smooth_of_geometricallyIrreducible X.hom

/-- An abelian variety is geometrically integral. -/
instance (priority := low) (X : Sch k) [IsAbelianVariety X] : GeometricallyIntegral X.hom :=
  geometricallyIntegral_of_smooth_of_geometricallyIrreducible' X

/-- An abelian variety (with its group structure) is commutative. -/
theorem isCommMonObj_of_isAbelianVariety (X : Sch k) [IsAbelianVariety X] [GrpObj X] :
    IsCommMonObj X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral X

end Work.AbVar
