/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Derived
import Submission.Work.DescentGeom.Geom
import Submission.Work.DescentGeom.AbelJacobi
import Submission.Work.DescentGeom.univ_and_epi
import Submission.Work.CurveBasics.All
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the Jacobian package over `k`

This is the output of the geometric half of §3.7 of `NOTES_LEAD_jacobian_GC.md`: from the chart
datum `D : Input C P0` (the outputs of areas `GC` over the finite Galois extension `k'`, of area
`SY` (SY1), of area `CH` and of area `UP`) we build the Jacobian package

```
Work.DescentGeom.jacPkgExists (D) : Nonempty (Work.Packaging.JacPkg C P0)
```

whose `J` is the descended group chunk `D.J` (the quotient of `G'` by the Galois group).  The
individual constructions live in

* `Submission/Work/DescentGeom/Basic.lean` — the interface `Input` and the Galois-action plumbing;
* `Submission/Work/DescentGeom/Kit.lean` — the descent toolkit (`desc_of_invariant`,
  `map_injective`, naturality of the action and of the projection);
* `Submission/Work/DescentGeom/Transfer.lean` — base change of group schemes and of their
  geometric properties;
* `Submission/Work/DescentGeom/desc_{one,mul,inv,AJ}.lean` — the descent of the structure morphisms;
* `Submission/Work/DescentGeom/Group.lean` — `GrpObj D.J`;
* `Submission/Work/DescentGeom/Geom.lean` — properness, smoothness, geometric irreducibility,
  connectedness, separatedness of `D.J`;
* `Submission/Work/DescentGeom/AbelJacobi.lean` — the Abel–Jacobi map `AJ : C ⟶ D.J` and its
  base point;
* `Submission/Work/DescentGeom/univ_and_epi.lean` — the universal property of `AJ`.

`Work.DescentGeom.jacPkgExistsOver` is the form of the statement with the curve given as
`C : Over (Spec k)` with the hypotheses of the challenge (the extra inputs
`GeometricallyReduced`, `Ring.KrullDimLE 1` and `Nontrivial` are the three fields of
`Work.CurveBasics.Curve` that are not yet in Mathlib, see `Work.CurveBasics.ofOver`).
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory CategoryTheory.Obj
open CartesianMonoidalCategory Functor

universe u

namespace Work.DescentGeom

noncomputable section

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

/-- **The descent data of the Jacobian**: all the fields of `Derived` are proved in this area. -/
noncomputable def derived (D : Input C P0) : Derived D where
  grpObj := instGrpObjJ D
  isProper := Input.isProper_J D
  smooth := Input.smooth_J D
  geomIrred := Input.geomIrred_J D
  connected := Input.connected_J D
  AJ := AJ D
  AJ_pt := AJ_pt D
  univ₀ := fun A [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    f hf => (univ_and_epi D A).1 f hf
  epi₀ := fun A [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    u v h => (univ_and_epi D A).2 u v h

/-- **The Jacobian package of `C` at the `k`-point `P0`**, from the chart datum over `k'`. -/
theorem jacPkg_of_input (D : Input C P0) : Nonempty (Packaging.JacPkg C P0) :=
  jacPkg D (derived D)

/-- The same, for a curve given as a `k`-scheme `C : Over (Spec k)` with the hypotheses of the
challenge, and the three structure fields of `Work.CurveBasics.Curve` that are not yet in Mathlib
(`GeometricallyReduced`, `Ring.KrullDimLE 1` on the stalks, `Nontrivial`). -/
theorem jacPkgExistsOver (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left)
    (P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (D : Input (Work.CurveBasics.Curve.ofOver C hred hdim hnt).toOver P0) :
    Nonempty (Packaging.JacPkg C P0) :=
  jacPkg_of_input D

/-- **The shape of the challenge's `jacPkgExists`.**  If the rest of the drive supplies a chart
datum over a finite Galois extension for every `k`-point of `C` (areas `GC`, `CH`, `SY`(SY1) and
`UP`), then the challenge's `jacPkgExists` follows. -/
theorem jacPkgExists_of_inputs (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left)
    (h : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C,
      Nonempty (Input (Work.CurveBasics.Curve.ofOver C hred hdim hnt).toOver P0)) :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Packaging.JacPkg C P0) :=
  fun P0 => (h P0).elim fun D => jacPkgExistsOver C hred hdim hnt P0 D

end

end Work.DescentGeom
