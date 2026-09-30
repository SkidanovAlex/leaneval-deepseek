/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.Trivial.geometricallyIrreducible_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: the trivial branch

If the curve `C` has no `k`-point, the packaging sets `Jacobian C := 𝟙_ (Over (Spec k))`, the
terminal (trivial) group scheme. This file supplies the instances needed to fill the challenge's
holes in that branch:

* `GrpObj (𝟙_ (Over (Spec k)))` (Mathlib's group structure on the tensor unit),
* `IsProper`, `SmoothOfRelativeDimension 0` and `GeometricallyIrreducible` for the structure morphism
  of the terminal object, which is `𝟙 (Spec k)`.

The last of these needs `Submission.Work.Packaging.Trivial.geometricallyIrreducible_one`; the first
three are instances of Mathlib up to the identification `Over.hom (𝟙_ (Over S)) = 𝟙 S`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj

namespace Work.Packaging.Trivial

variable {k : Type u} [Field k]

/-- The structure morphism of the terminal object of `Over (Spec k)` is the identity. -/
theorem hom_tensorUnit_eq : (𝟙_ (Over (Spec (.of k)))).hom = 𝟙 (Spec (.of k)) := rfl

/-- The terminal object of `Over (Spec k)` is a group object. -/
noncomputable instance instGrpObjUnit : GrpObj (𝟙_ (Over (Spec (.of k)))) := inferInstance

/-- The identity of `Spec k` is smooth. -/
theorem smooth_id : Smooth (𝟙 (Spec (.of k))) := by infer_instance

/-- The identity of `Spec k` is proper. -/
theorem isProper_id : IsProper (𝟙 (Spec (.of k))) := by infer_instance

/-- The identity of `Spec k` is smooth of relative dimension `0`. -/
theorem smoothOfRelativeDimension_zero_id :
    SmoothOfRelativeDimension 0 (𝟙 (Spec (.of k))) := by infer_instance

/-- The terminal object of `Over (Spec k)` is proper over `Spec k`. -/
instance instIsProperUnit : IsProper (𝟙_ (Over (Spec (.of k)))).hom := isProper_id

/-- The terminal object of `Over (Spec k)` is smooth over `Spec k`. -/
instance instSmoothUnit : Smooth (𝟙_ (Over (Spec (.of k)))).hom := smooth_id

/-- The terminal object of `Over (Spec k)` is smooth of relative dimension `0` over `Spec k`. -/
instance instSmoothOfRelativeDimensionUnit :
    SmoothOfRelativeDimension 0 (𝟙_ (Over (Spec (.of k)))).hom := smoothOfRelativeDimension_zero_id

/-- `Spec k` is geometrically irreducible over `k`. -/
instance instGeomIrredSpecId : GeometricallyIrreducible (𝟙 (Spec (.of k))) :=
  geometricallyIrreducible_one

/-- The terminal object of `Over (Spec k)` is geometrically irreducible over `Spec k`. -/
instance instGeomIrredUnit : GeometricallyIrreducible (𝟙_ (Over (Spec (.of k)))).hom := by
  rw [hom_tensorUnit_eq]
  infer_instance

/-- The underlying scheme of the terminal object of `Over (Spec k)` is `Spec k`, which is
connected. -/
instance instConnectedUnit : ConnectedSpace (𝟙_ (Over (Spec (.of k)))).left := by
  change ConnectedSpace (Spec (.of k))
  infer_instance

end Work.Packaging.Trivial
