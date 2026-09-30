/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.grpObj_of_descent
import Submission.Work.DescentGeom.desc_one
import Submission.Work.DescentGeom.desc_mul
import Submission.Work.DescentGeom.desc_inv
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the group structure of the descended Jacobian

The multiplication, unit and inverse of the Jacobian `J = D.J` over `k` are the descents of the
corresponding structure morphisms of the group chunk `G' = D.G'` over `k'` (the lemmas `desc_mul`,
`desc_one`, `desc_inv` of this area).  The axioms are reflected along the faithful base change
functor by `grpObj_of_descent`, using the transported group structure
`GrpObj.ofIso D.bcIso.symm` on the base change `(D.J)_{k'} ≅ G'`.

This is the `GrpObj` field of `Work.DescentGeom.Derived`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory CategoryTheory.Obj
open CartesianMonoidalCategory Functor

universe u

namespace Work.DescentGeom

noncomputable section

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C} (D : Input C P0)

/-! ### The structure morphisms of `D.J` -/

/-- The multiplication of `D.J`: the descent of the multiplication of the group chunk. -/
noncomputable def mulJ : D.J ⊗ D.J ⟶ D.J := (desc_mul D).choose

/-- The unit of `D.J`. -/
noncomputable def oneJ : 𝟙_ (Sch k) ⟶ D.J := (desc_one D).choose

/-- The inverse of `D.J`. -/
noncomputable def invJ : D.J ⟶ D.J := (desc_inv D).choose

/-- The base change of the multiplication is the multiplication of the group chunk, transported
along the descent isomorphism `D.bcIso`. -/
theorem map_mulJ : (bcFun k D.k').map (mulJ D) =
    (CartesianMonoidalCategory.prodComparisonIso (bcFun k D.k') D.J D.J).hom ≫
      (D.bcIso.hom ⊗ₘ D.bcIso.hom) ≫ μ[D.G'] ≫ D.bcIso.inv :=
  (desc_mul D).choose_spec

/-- The base change of the unit is the unit of the group chunk, transported along `D.bcIso`. -/
theorem map_oneJ : (bcFun k D.k').map (oneJ D) =
    (CartesianMonoidalCategory.preservesTerminalIso (bcFun k D.k')).hom ≫
      η[D.G'] ≫ D.bcIso.inv :=
  (desc_one D).choose_spec

/-- The base change of the inverse is the inverse of the group chunk, transported along
`D.bcIso`. -/
theorem map_invJ : (bcFun k D.k').map (invJ D) =
    D.bcIso.hom ≫ ι[D.G'] ≫ D.bcIso.inv :=
  (desc_inv D).choose_spec

/-! ### The group structure on `D.J` -/

/-- **`D.J` is a group scheme over `k`**: the existence statement obtained from
`grpObj_of_descent`, with the identification of its structure morphisms.  Kept as a `def` (not an
`instance`) so that the equations `grpObjJ_mul`, `grpObjJ_one`, `grpObjJ_inv` below are definitional
applications of its `choose_spec`. -/
noncomputable def grpObjJExists :
    ∃ m : GrpObj D.J, m.mul = mulJ D ∧ m.one = oneJ D ∧ m.inv = invJ D := by
  let hgrp : GrpObj (bc D.k' D.J) := GrpObj.ofIso D.bcIso.symm
  letI := hgrp
  refine (@grpObj_of_descent k D.k' _ _ _ D.J hgrp (mulJ D) (oneJ D) (invJ D) ?_ ?_ ?_)
  · rw [map_mulJ, GrpObj.ofIso_mul D.bcIso.symm]
    rfl
  · rw [map_oneJ, MonObj.ofIso_one D.bcIso.symm]
    rfl
  · rw [map_invJ, GrpObj.ofIso_inv D.bcIso.symm]
    rfl

/-- The group structure on the Jacobian `D.J`. -/
@[instance_reducible]
noncomputable def grpObjJ : GrpObj D.J := (grpObjJExists D).choose

theorem grpObjJ_mul : (grpObjJ D).mul = mulJ D := (grpObjJExists D).choose_spec.1

theorem grpObjJ_one : (grpObjJ D).one = oneJ D := (grpObjJExists D).choose_spec.2.1

theorem grpObjJ_inv : (grpObjJ D).inv = invJ D := (grpObjJExists D).choose_spec.2.2

/-- `D.J` is a group scheme over `k`. -/
noncomputable instance instGrpObjJ : GrpObj D.J := grpObjJ D

/-- The unit of `D.J` is `oneJ`. -/
theorem eta_J : η[D.J] = oneJ D := grpObjJ_one D

/-- The multiplication of `D.J` is `mulJ`. -/
theorem mul_J : μ[D.J] = mulJ D := grpObjJ_mul D

/-- The inverse of `D.J` is `invJ`. -/
theorem inv_J : ι[D.J] = invJ D := grpObjJ_inv D

end

end Work.DescentGeom
