/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the glued group chunk `G D`: the exported API

Import this module to get the whole chapter of area GC of the Jacobian drive
(`Submission/Work/NOTES_LEAD_jacobian_GC.md` §3.6), for a field `K`, a curve `C : Curve K`,
a base point `P0 : 𝟙_ (Sch K) ⟶ C.toOver` and a chart datum `D : Input C P0`:

* the chart datum `Work.GroupChunk.Input C P0` and its API (`Sym`, `divOf`, `picOf`,
  `InChart`, `E`, `EDiv`, `cov'`, …) — `Interface.lean`;
* the transitions `σ`, `W`, `U`, `Uι`, `t` — `Defs.lean`, `Transitions.lean`,
  `Gluing/Transitions.lean`, `t_inv.lean`;
* the gluing datum and the glued scheme `GSch D` — `Gluing/Data.lean`, and the gluing
  `glued_exists.lean`;
* the group chunk `D.G = GSch D`, its charts `D.chart i`, the class map `D.cls` and the
  point-level description of the gluing (`D.cls_chart`, `D.cls_bijective`,
  `D.eq_iff_class`, `D.hom_ext_cls`) — `Group.lean`, `Gluing/Chart.lean`;
* the Abel–Jacobi morphism `D.AJSym` with `D.cls_AJSym` and `D.AJSym_surjective` —
  `AJSym.lean`;
* the geometry of `G D` as *instances* (`IsProper`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `QuasiSeparated`, `GeometricallyIntegral`, `GeometricallyIrreducible`,
  `GeometricallyReduced`, `ConnectedSpace`, `IsIntegral`, `IsReduced`,
  `IsLocallyNoetherian`) — `Assembly.lean` and the directories `Finiteness`, `QuasiSep`,
  `Separated`, `Proper`, `GeomProps`;
* the universal property of the gluing (`Desc.desc_exists`, `desc`, `desc_chart`) —
  `Desc/desc_exists.lean`, `Desc/Basic.lean`;
* the Abel–Jacobi map `AJ₀`, the group law (`D.mul`, `D.inv`, `D.one`, `D.cls_mul`,
  `D.cls_inv`, `D.cls_one`, `GrpObj (G D)`) and `Smooth (G D).hom` — `AJ0Basic.lean`,
  `GroupLaw/`, `AJ/`, `Smooth/`, `Genus/`.
-/
import Submission.Work.GroupChunk.Interface
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Glue
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.AJ0Basic
import Submission.Work.GroupChunk.Assembly
import Submission.Work.GroupChunk.Desc.Basic
import Submission.Work.GroupChunk.AJ.cls_AJ0
import Submission.Work.GroupChunk.Genus.one_le_g
import Submission.Work.GroupChunk.Smooth.smooth_G
import Submission.Work.GroupChunk.Smooth.Instance
import Submission.Work.GroupChunk.GroupLaw.Basic
import Submission.Work.GroupChunk.GroupLaw.grpObj_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

