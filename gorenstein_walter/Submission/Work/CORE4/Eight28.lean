/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — design pass 28: §4 (8) is CLOSED; route L is down to the count leaves

Thin re-export of the lead's design file `Submission/Work/_design_gw/Core28.lean`
(namespace `Work.GW2.C28`), which proves (axioms clean, no `sorry`):

* `Work.GW2.C28.case2EightImpl_holds (I) : Case2EightImpl I` — **§4 (8) unconditionally**
  (both `eightIndexLeaf_of_case3` and `eightExceptLeaf_of_case3` are proved from
  `case3InvNormal` + `U_eq_of_invNormal`; the case-3 input is the TRUE Bender input
  `I_U(s) = F(U) ⊓ C_G(Q)`, derived from `Case2Pre.B0_eq`, `F_def`, `F_ti`, `thm26` — not the
  strictly stronger (α) of `CORE4/AlphaDefs.lean`, which must NOT be dispatched);
* `Work.GW2.C28.case2False_routeL28' (I) (hL2) (hCopy) (hFour) (hY) (hZ) : Case2FalseProp`
  — **route L with the five design-27 count leaves as its only inputs**;
* `Work.GW2.C28.case2False_routeL28 (I) (hH : Case3HhatProp I) ...` — the same with the case-3
  context input exposed.

`Work.GW2.C28` imports `Submission.Work.CORE4.Final3`, `…EightIndexOfAlpha`,
`…EightDichotomyOfTrich`, `…EightTrich9Holds` and `…Case2EightCase3U9plus` from this area.

The area's own leaves are stated as `Work.CORE4.PerY` / `Work.CORE4.PerZ`
(`CopyLocalProp → FourCentProp I → PerYProp/PerZProp I`) and `Work.CORE4.CopyLocal27`
(`L2pLocalProp → CopyLocalProp`); instantiating them in `case2False_routeL28'` gives
`case2False_28_all` below as soon as `CopyLocal27` is proved.
-/
import Mathlib
import Submission.Work.LEAD.Core28
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.CopyLocal27
import Submission.Work.CORE4.L2pLocal
import Submission.Work.CORE4.PerY
import Submission.Work.CORE4.PerZ
import Submission.Work.CORE4.FourCent
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.CopyLocal27
import Submission.Work.CORE4.L2pLocal

namespace Work.GW2

/-- **Route L with the design-27 count leaves named**: §4 (1)–(12) of Bender 1965/1981 with every
leaf of areas CORE4 except the count now proved. -/
theorem case2False_28 (I : C4Inputs10)
    (hL2 : Work.GW2.C27.L2pLocalProp)
    (hCopy : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I.toC4Inputs)
    (hY : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerYProp I.toC4Inputs)
    (hZ : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerZProp I.toC4Inputs) : Case2FalseProp :=
  Work.GW2.C28.case2False_routeL28' I hL2 hCopy hFour hY hZ

/-- The same, with the proved `Work.CORE4.PerY` plugged in for `hY`. -/
theorem case2False_28_perY (I : C4Inputs10)
    (hL2 : Work.GW2.C27.L2pLocalProp)
    (hCopy : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I.toC4Inputs)
    (hZ : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerZProp I.toC4Inputs) : Case2FalseProp :=
  Work.GW2.C28.case2False_routeL28' I hL2 hCopy hFour (Work.CORE4.PerY I.toC4Inputs) hZ

/-- **The area's deliverable with all the leaves of this round plugged in**: `Case2FalseProp` from
the two remaining design-27 inputs only — the `L₂(q)` input `hL2` and its transport `hCopy`.
`Work.CORE4.FourCent`, `Work.CORE4.PerY` and `Work.CORE4.PerZ` are PROVED and are used here. -/
theorem case2False_28_final (I : C4Inputs10)
    (hL2 : Work.GW2.C27.L2pLocalProp)
    (hCopy : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp) : Case2FalseProp :=
  Work.GW2.C28.case2False_routeL28' I hL2 hCopy (Work.CORE4.FourCent I.toC4Inputs)
    (Work.CORE4.PerY I.toC4Inputs) (Work.CORE4.PerZ I.toC4Inputs)

/-- **The area's deliverable from ONE input**: `Case2FalseProp` from
`Work.GW2.C27.L2pLocalProp` alone.

`Work.CORE4.CopyLocal27` (the transport `L2pLocalProp → CopyLocalProp`) is PROVED, and so are
`Work.CORE4.FourCent`, `Work.CORE4.PerY`, `Work.CORE4.PerZ` and everything else on the route — so
the whole §4 elimination of area CORE4 hangs on the single-copy `L₂(q)` input. -/
theorem case2False_28_one (I : C4Inputs10) (hL2 : Work.GW2.C27.L2pLocalProp) : Case2FalseProp :=
  Work.GW2.case2False_28_final I hL2 Work.CORE4.CopyLocal27

/-- **THE AREA'S DELIVERABLE, UNCONDITIONAL** (modulo the cross-area bundle `C4Inputs10`):
Bender's §4 elimination of Case 2, `Work.GW2.Case2FalseProp`.

Every leaf of the §4 chain is proved: §4 (1)–(5) `Work.CORE4.Case2Setup9`, (6)
`case2SixImpl9_holds`, (7) `Case2SevenImpl9`, (8) `Work.GW2.C28.case2EightImpl_holds`, the `A₇`
chain `Case2NotA7Impl9_holds`, step (9) `Work.GW2.Case2NineImpl9_holds`, the count
`Case2CountImpl9_of_amalgam` with `FourCent`/`PerY`/`PerZ`/`CopyLocal27`, the `L₂(q)` input
`Work.CORE4.L2pLocal`, and the arithmetic `Work.GW2.case2Arith`. -/
theorem case2False_deliverable (I : C4Inputs10) : Case2FalseProp :=
  Work.GW2.case2False_28_one I Work.CORE4.L2pLocal

end Work.GW2
