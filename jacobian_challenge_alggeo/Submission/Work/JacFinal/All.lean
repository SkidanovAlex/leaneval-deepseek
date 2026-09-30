/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.Basic
import Submission.Work.JacFinal.GalAct
import Submission.Work.JacFinal.Assembly
import Submission.Work.JacFinal.Orbit
import Submission.Work.JacFinal.ChartDict
import Submission.Work.JacFinal.PermQuot
import Submission.Work.JacFinal.GalSym
import Submission.Work.JacFinal.Main
import Submission.Work.JacFinal.rr7_of_rochData
import Submission.Work.JacFinal.genus_zero_no_input

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the whole chapter

Import this module to get the final assembly of the Jacobian challenge:

* the construction of the semilinear Galois action on the group chunk
  (`Work.JacFinal.Gal.Chunk`, `Work.JacFinal.Inputs.toChunk`);
* the assembly of the chart datum `Work.DescentGeom.Input` from the areas of the drive
  (`Work.JacFinal.Inputs.nonempty_input`), with the `Γ`-stable affine cover *proved*
  (`Work.JacFinal.Inputs.cover_of_chart_orbit`, `Work.JacFinal.Inputs.cover_of_affine_orbit`,
  `…cover_iff_affineOrbit`), together with the chart/class dictionary
  (`Work.JacFinal.Inputs.mem_chartRange_of_inChart`) that reduces its remaining input to area
  `CH`'s equivariant covering (`Work.JacFinal.CovOrbit`);
* the wiring of the challenge's `jacPkgExists` (`Work.JacFinal.jacPkgExists`);
* §1.4(b), (c) of the lead's design (`Work.JacFinal.GalSym`): the Galois action on the `n`-fold
  product of `C_{k'}` and on its symmetric power `Sym^g C_{k'}`, and the equivariance of
  `AJSym` (`Work.JacFinal.Inputs.AJSym_galAct`) — conditional only on the single interface
  property `Work.JacFinal.Inputs.PermQuot` (the invariance of the quotient map under `S_n`;
  gap (G5) of `NOTES.md` §2.2).

It also contains the discharge of the `rr7` field of `Work.GroupChunk.Input` from area `RR`
(`Work.JacFinal.rr7_of_rochData`).

The input vocabulary is `Work.JacFinal.Inputs` (the outputs of the areas of the drive over the
finite Galois extension, in their exact current Lean form); `Work.JacFinal.Data` bundles it per
base point together with the two chart-level items of §1.4 that turn `hcover` into a theorem
(`IsAffineOpen V` and the orbit-in-one-chart statement).
-/
