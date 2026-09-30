/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area PR (`Submission/Work/SpecLin`) — the whole area

Import this module to get all of area `PR` of the Jacobian drive (item 3.4 of
`NOTES_LEAD_jacobian_GC.md`): the conventions, the point/divisor API, the interfaces of areas
`CB` and `SY`, the commutative algebra, and the main theorem
`Work.SpecLin.specLin` — specialisation of linear equivalence over an arbitrary valuation ring —
with its mathematical core `Work.SpecLin.Core.linEquiv_of_sections`.

* `Work.SpecLin.Sch`, `Work.SpecLin.specOf`, `Work.SpecLin.RPt`, `Work.SpecLin.FPt`,
  `Work.SpecLin.RPt.map`, `Work.SpecLin.genPt`, `Work.SpecLin.closedPt`, `Work.SpecLin.Dv`,
  `Work.SpecLin.LinEquiv` — the shared conventions of §2 (`Conventions.lean`);
* `Work.SpecLin.ptLeft`, `Work.SpecLin.ptToPoint`, `Work.SpecLin.ptPlace`,
  `Work.SpecLin.ptDiv`, `Work.SpecLin.Points.ptToPoint_isClosed`,
  `Work.SpecLin.Points.ptDiv_deg`, `Work.SpecLin.Points.ptDiv_complete` — points of a
  base-changed curve and their divisors (`Points/`);
* `Work.SpecLin.DivBase`, `Work.SpecLin.SymGeom` — the interfaces of areas `CB` and `SY`
  (`Interface.lean`), together with the definitional agreement with area `GB`
  (`Bridge.lean`, not imported here so that this module stays independent of `GB`);
* `Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing`, the `Content` lemmas — the
  commutative algebra of the core argument (`Chart/`, `Content/`);
* `Work.SpecLin.Core.linEquiv_of_sections` — specialisation of linear equivalence for two
  `n`-tuples of `R`-points of `C` (`Core/linEquiv_of_sections.lean`): the mathematical heart;
* `Work.SpecLin.specLin` — the main theorem of the area (`specLin.lean`).
-/
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.ptToPoint_isClosed
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Points.ptDiv_deg
import Submission.Work.SpecLin.Points.ptDiv_complete
import Submission.Work.SpecLin.Interface
import Submission.Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.SpecLin.specLin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

