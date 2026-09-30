/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.galActProdMap_naturality
import Submission.Work.DescentGeom.grpObj_of_descent
import Submission.Work.DescentGeom.desc_one
import Submission.Work.DescentGeom.desc_mul
import Submission.Work.DescentGeom.desc_inv
import Submission.Work.DescentGeom.desc_AJ
import Submission.Work.DescentGeom.geometricallyIrreducible_of_bc
import Submission.Work.DescentGeom.isSeparated_of_bc
import Submission.Work.DescentGeom.Group
import Submission.Work.DescentGeom.Geom
import Submission.Work.DescentGeom.AbelJacobi
import Submission.Work.DescentGeom.univ_and_epi
import Submission.Work.DescentGeom.Derived
import Submission.Work.DescentGeom.Main
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the geometric half of Galois descent (area DS)

Import this module to get the whole chapter: the interface `Work.DescentGeom.Input` (the outputs of
areas `GC`, `CH`, `SY`(SY1) and `UP` over a finite Galois extension `k'/k`, as named hypotheses),
the descent toolkit, the constructed group scheme `D.J`, its geometric properties, the
Abel–Jacobi map and the universal property, and finally

```
Work.DescentGeom.jacPkgExistsOver : Nonempty (Work.Packaging.JacPkg C P0)
```

for a curve `C : Over (Spec k)` with the hypotheses of the challenge and a `k`-point `P0`, given the
chart datum over `k'`.  See `Submission/Work/DescentGeom/NOTES.md` for the design and the interface
in detail.
-/
