/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the `A₄` chain of design passes 15/17, assembled

The leaves `A4i`, `A4a`, `A4a2`, `A4s`, `A4b`, `A4c2` are all proved in this area.  Here they are
composed, via the proved assembly `Work.CORE4.C15.invNormalFrom_of_parts2` (`Defs17.lean`), into

* `Work.CORE4.A7InvNormalFrom : A7InvNormalFromProp I` — i.e. `¬ Case2InvNormal` from the data
  `(1)`–`(5)` + `A7Facts1/2` + `A7UData` (no contested `K = Z(U)` hypothesis);
* `Work.CORE4.A7InvNormalProp_of_from : A7InvNormalFromProp I → A7InvNormalProp I` — the bridge to
  the design-10 name (`A7Facts3 → A7UData`, dropping the conjunct `K = Z(U)`), so that the older
  assembly `Work.GW2.notA7_of_leaves` can consume the new chain.

This closes the `A₃ ↔ A₄` circle of design pass 10: the exceptional case `I_U(s) ⊴ Ĥ` is excluded by
the new route, and the `A₇` chain no longer needs `K = Z(U)` as an input.
-/
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Defs17
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A4a2
import Submission.Work.CORE4.A4s
import Submission.Work.CORE4.A4b
import Submission.Work.CORE4.A4c2

namespace Work.CORE4

open Work.GW2 Subgroup

/-- **The `A₄` chain, composed.**  `¬ Case2InvNormal` from the design-pass-15 hypotheses
(`A4i`/`A4a2`/`A4s`/`A4b`/`A4c2` are all proved in the area). -/
theorem A7InvNormalFrom (I : C4Inputs) : C15.A7InvNormalFromProp I :=
  C15.invNormalFrom_of_parts2 I (A4a2 I) (A4s) (A4b I) (A4c2 I)

/-- Bridge to the design-10 statement `A7InvNormalProp` (whose hypotheses use `A7Facts3`): the
conclusion `¬ Case2InvNormal` depends only on `A7UData`, which is `A7Facts3` minus the conjunct
`K = Z(U)`. -/
theorem A7InvNormalProp_of_from (I : C4Inputs) (h : C15.A7InvNormalFromProp I) :
    A7InvNormalProp I :=
  fun G _ _ B C h9 hA f1 f2 f3 =>
    h G B C h9 hA f1 f2 ⟨f3.1, f3.2.1, f3.2.2.1, f3.2.2.2.2⟩

/-- The design-10 `A7InvNormalProp` holds in this area, via the design-15/17 route. -/
theorem A7InvNormalProp_holds (I : C4Inputs) : A7InvNormalProp I :=
  A7InvNormalProp_of_from I (A7InvNormalFrom I)

end Work.CORE4
