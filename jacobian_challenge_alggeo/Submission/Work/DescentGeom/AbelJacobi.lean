/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Group
import Submission.Work.DescentGeom.desc_AJ
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the Abel–Jacobi map over `k`

The Abel–Jacobi map `AJ : C ⟶ D.J` over `k` is the descent of the Abel–Jacobi map
`D.AJ' : C_{k'} ⟶ G'` of area `GC` (the lemma `desc_AJ` of this area).  Its base change is
`(D.AJ' ≫ D.bcIso.inv)`, and it sends the base point `P0` to the origin of the group scheme
`D.J` because `D.AJ'_pt` says the same over `k'` and `η[D.J]` is the descent of the unit.
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

/-- The Abel–Jacobi map of `D.J` based at `P0`: the descent of the Abel–Jacobi map over `k'`. -/
noncomputable def AJ : C ⟶ D.J := (desc_AJ D).choose

/-- The base change of the Abel–Jacobi map is the Abel–Jacobi map of the group chunk, transported
along the descent isomorphism. -/
theorem map_AJ : (bcFun k D.k').map (AJ D) = D.AJ' ≫ D.bcIso.inv := (desc_AJ D).choose_spec

/-- The underlying morphism of schemes of the base change of `AJ`. -/
theorem map_AJ_left : ((bcFun k D.k').map (AJ D)).left = D.AJ'.left ≫ D.bcIso.inv.left :=
  congrArg Over.Hom.left (map_AJ D)

/-- **`AJ` sends the base point to the origin.** -/
theorem AJ_pt : P0 ≫ AJ D = η[D.J] := by
  rw [eta_J D]
  refine map_injective (k := k) (k' := D.k') _ _ ?_
  show (bcFun k D.k').map (P0 ≫ AJ D) = (bcFun k D.k').map (oneJ D)
  rw [Functor.map_comp, map_AJ, map_oneJ, ← Category.assoc, D.AJ'_pt, Category.assoc]

end

end Work.DescentGeom
