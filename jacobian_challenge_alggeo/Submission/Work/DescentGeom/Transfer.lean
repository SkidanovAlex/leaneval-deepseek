/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Kit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — transfer of structure along the base change `k'/k`

This file records how the structure of a `k`-scheme is seen after the base change to `k'`, and
conversely.  The forward directions (`GrpObj`, properness, smoothness, ...) are the statements that
an abelian variety stays an abelian variety after base change (needed to apply the universal
property of area `UP` over `k'` to `A_{k'}`); the backward directions (`GeometricallyIrreducible`,
separatedness) are the descent statements used for the geometric properties of `J`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory CategoryTheory.Obj
open CartesianMonoidalCategory Functor

universe u

namespace Work.DescentGeom

noncomputable section

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ### Forward: base change of a group scheme and of its geometric properties -/

instance grpObj_bc (A : Sch k) [GrpObj A] : GrpObj (bc k' A) :=
  Functor.grpObjObj

instance isProper_bc (A : Sch k) [IsProper A.hom] : IsProper (bc k' A).hom := by
  rw [Work.Descent.baseChange_hom]; infer_instance

instance smooth_bc (A : Sch k) [Smooth A.hom] : Smooth (bc k' A).hom := by
  rw [Work.Descent.baseChange_hom]; infer_instance

instance locallyOfFiniteType_bc (A : Sch k) [LocallyOfFiniteType A.hom] :
    LocallyOfFiniteType (bc k' A).hom := by
  rw [Work.Descent.baseChange_hom]; infer_instance

instance isSeparated_bc (A : Sch k) [IsSeparated A.hom] : IsSeparated (bc k' A).hom := by
  rw [Work.Descent.baseChange_hom]; infer_instance

instance geomIrred_bc (A : Sch k) [GeometricallyIrreducible A.hom] :
    GeometricallyIrreducible (bc k' A).hom := by
  rw [Work.Descent.baseChange_hom]; infer_instance

/-- The terminal comparison of the base change functor is the `Over`-unit comparison
`OplaxMonoidal.η`. -/
theorem preservesTerminalIso_eq_oplax :
    (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom =
      OplaxMonoidal.η (bcFun k k') := by
  ext
  rw [Over.preservesTerminalIso_pullback]
  rfl

/-- The unit of a base-changed group object is the base change of the unit:
`F.map η[A] = ε ≫ η[A_{k'}]`, in the form used for the universal property over `k'`. -/
theorem map_eta_bc (A : Sch k) [GrpObj A] :
    (bcFun k k').map η[A] =
      (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom ≫ η[bc k' A] := by
  rw [Functor.obj.η_def, preservesTerminalIso_eq_oplax, ← Category.assoc, Monoidal.η_ε,
    Category.id_comp]

/-- The multiplicative structure of a base-changed group object is the base change of the
multiplication: the equation `F.map μ[A] = pc ≫ μ[A_{k'}]` used for the descent of the group
structure. -/
theorem map_mul_bc (A : Sch k) [GrpObj A] :
    (bcFun k k').map μ[A] =
      (CartesianMonoidalCategory.prodComparisonIso (bcFun k k') A A).hom ≫ μ[bc k' A] := by
  rw [Functor.obj.μ_def, Monoidal.μ_of_cartesianMonoidalCategory, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

end

end Work.DescentGeom
