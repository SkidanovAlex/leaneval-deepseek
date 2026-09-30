/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Basic
import Submission.Work.Packaging.Basic
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the descended Jacobian package

The interface `Input` of `Basic.lean` collects the *primitive* outputs of the other areas (the
group chunk `G'` over the finite Galois extension `k'`, the semilinear Galois action, the descent
isomorphism `J_{k'} ≅ G'` of SY1/Speiser, the Abel–Jacobi map over `k'` and the universal property
over `k'` of area `UP`).  The structure `Derived` below records the *consequences* for the
`k`-scheme `J`: the group structure, the geometric properties, the Abel–Jacobi map over `k` and its
universal property.  Each field is a theorem to be proved in this area:

* `grpObj`  — `Submission/Work/DescentGeom/Group.lean` (descents `desc_mul`, `desc_one`, `desc_inv`
  plus `grpObj_of_descent`);
* `isProper`, `smooth`, `geomIrred`, `connected` — `Submission/Work/DescentGeom/Geom.lean`;
* `AJ`, `AJ_pt` — `Submission/Work/DescentGeom/AbelJacobi.lean`;
* `univ₀`, `epi₀` — `Submission/Work/DescentGeom/Univ.lean`.

`Work.DescentGeom.jacPkg` assembles them into `Work.Packaging.JacPkg C P0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

namespace Work.DescentGeom

noncomputable section

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

/-- The descendants of the chart datum over `k'`: the group structure on `J`, its geometric
properties, the Abel–Jacobi map over `k` and the universal property. -/
structure Derived (D : Input C P0) where
  /-- `J` is a group scheme over `k`. -/
  [grpObj : GrpObj D.J]
  /-- `J` is proper over `k`. -/
  [isProper : IsProper D.J.hom]
  /-- `J` is smooth over `k`. -/
  [smooth : Smooth D.J.hom]
  /-- `J` is geometrically irreducible over `k`. -/
  [geomIrred : GeometricallyIrreducible D.J.hom]
  /-- the underlying space of `J` is connected. -/
  [connected : ConnectedSpace D.J.left]
  /-- the Abel–Jacobi map based at `P0`. -/
  AJ : C ⟶ D.J
  /-- it sends `P0` to the origin. -/
  AJ_pt : P0 ≫ AJ = η[D.J]
  /-- the universal property of the Abel–Jacobi map. -/
  univ₀ : ∀ (A : Sch k) [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom]
    [GrpObj A] (f : C ⟶ A), P0 ≫ f = η[A] → ∃! g : D.J ⟶ A, f = AJ ≫ g
  /-- `AJ` generates `J`. -/
  epi₀ : ∀ (A : Sch k) [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom]
    [GrpObj A] (u v : D.J ⟶ A), AJ ≫ u = AJ ≫ v → u = v

/-- **The Jacobian package of `C` at `P0`**, assembled from the descent data. -/
theorem jacPkg (D : Input C P0) (h : Derived D) : Nonempty (Packaging.JacPkg C P0) :=
  ⟨{ J := D.J
     instGrpObj := h.grpObj
     instIsProper := h.isProper
     instGeomIrred := h.geomIrred
     instSmooth := h.smooth
     instConnected := h.connected
     AJ₀ := h.AJ
     AJ₀_pt := h.AJ_pt
     univ₀ := h.univ₀
     epi₀ := h.epi₀ }⟩

end

end Work.DescentGeom
