/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the §4 elimination with the proved leaves plugged in

`Final.case2False_full` is the area's kernel: it takes *every* leaf of the §4 elimination as a
hypothesis.  This file records how much of it is now discharged: `case2False_remains` has only

* `Case2Setup9` (§4 (1)–(5) + the Sylow choice) — in flight (its `Case2Setup9S` core),
* `Case2Six` (§4 (6)) — in flight,
* `A7U` (`A7Facts3`) and `A7InvNormal` (`A7Facts4`) — the two `A₇` inputs of the design-10 chain,
  whose design-15/17 replacement (`A4a2` — PROVED, `A4s` — PROVED, `A4b`, `A4c2`) lands in
  `Defs17.lean` / `NotA7Defs.lean`,
* `A7Coset` (A6) — in flight,
* `Case2Seven` (§4 (7)) — in flight,
* `Case2Count` (§4 (7)–(12)) — in flight,

as hypotheses.  Everything else is proved in the area and imported here:
`Case2SixEmbed`, `A7K` (A1), `A7V` (A2), `A7IndexH` (A5), `A7SmallIndex` (A7), `CoreIndex` (A8),
`NineShape` (N1), `NineK` (N2), `NineCenter` (N3), `NineOuterInv` (N5a), `NineR` (N5b),
`NineConj9` + `DihFourConj` (N5c), `NineRy` (N5d), `Case2Eight`, `A7S4`, `case2Arith`.
-/
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Layer
import Submission.Work.CORE4.Final

import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.A7K
import Submission.Work.CORE4.A7V
import Submission.Work.CORE4.A7IndexH
import Submission.Work.CORE4.A7SmallIndex
import Submission.Work.CORE4.CoreIndex
import Submission.Work.CORE4.NineShape
import Submission.Work.CORE4.NineK
import Submission.Work.CORE4.NineCenter
import Submission.Work.CORE4.NineOuterInv
import Submission.Work.CORE4.NineR
import Submission.Work.CORE4.NineRy
import Submission.Work.CORE4.DihFourConj
import Submission.Work.CORE4.NineImpl9.NineConj9
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.NotA7Assembly

namespace Work.GW2

open Subgroup

/-- **The §4 elimination with the proved leaves discharged.**  Under `I : C4Inputs10` (the bundle
plus `l2outer`), the seven leaf hypotheses below give `Case2FalseProp`. -/
theorem case2False_remains (I : C4Inputs10)
    (hSetup : Case2SetupImpl9 I.toC4Inputs) (hSix : Case2SixImpl I.toC4Inputs)
    (hThree : A7UProp I.toC4Inputs) (hFour : A7InvNormalProp I.toC4Inputs)
    (hCoset : A7CosetProp I.toC4Inputs) (hSeven : Case2SevenImpl I.toC4Inputs)
    (hCount : Case2CountImpl I.toC4Inputs) : Case2FalseProp :=
  case2False_full I hSetup hSix
    (Work.CORE4.Case2SixEmbed I.toC4Inputs) hSeven
    (Work.CORE4.Case2Eight I.toC4Inputs)
    (Work.CORE4.A7K I.toC4Inputs) (Work.CORE4.A7V I.toC4Inputs) hThree hFour
    (Work.CORE4.A7IndexH I.toC4Inputs) hCoset (Work.CORE4.A7SmallIndex I.toC4Inputs)
    Work.CORE4.CoreIndex
    (Work.CORE4.NineShape I.toC4Inputs) (Work.CORE4.NineK I.toC4Inputs)
    (Work.CORE4.NineCenter I.toC4Inputs) (Work.CORE4.NineOuterInv I.toC4Inputs)
    (Work.CORE4.NineR I)
    (Work.CORE4.NineImpl9.NineConj9 I.toC4Inputs Work.CORE4.DihFourConj)
    (Work.CORE4.NineRy I.toC4Inputs) hCount

/-! ## The two chains that are complete -/

/-- **Step (9) is proved**: `Case2NineImpl9` from the design-10 assembly `nine_of_leaves` with
every leaf discharged (N1 `NineShape`, N2 `NineK`, N3 `NineCenter`, N5a `NineOuterInv`,
N5b `NineR`, N5c `NineConj9` + `DihFourConj`, N5d `NineRy`, and `SixEmbedProp`). -/
theorem Case2NineImpl9_holds (I : C4Inputs10) : Case2NineImpl9 I.toC4Inputs :=
  nine_of_leaves I.toC4Inputs (Work.CORE4.Case2SixEmbed I.toC4Inputs)
    (Work.CORE4.NineShape I.toC4Inputs) (Work.CORE4.NineK I.toC4Inputs)
    (Work.CORE4.NineCenter I.toC4Inputs) (Work.CORE4.NineOuterInv I.toC4Inputs)
    (Work.CORE4.NineR I)
    (Work.CORE4.NineImpl9.NineConj9 I.toC4Inputs Work.CORE4.DihFourConj)
    (Work.CORE4.NineRy I.toC4Inputs)

/-- **The deliverable from the eight remaining hypotheses**: the §4 (1)–(5)+(6) leaves `Setup9` and
`Six9`, the §4 (7) leaf `Seven`, the four remaining `A₇` leaves
(`A7UMinusProp` = A3m, `A7IndexHWeakProp` = A5, `A7CosetWeakProp` = A6,
`A7SmallIndexWeakProp` = A7) and the counting leaf `Count`.

Everything else is proved here: `Case2Eight` (§4 (8)), the `A₄` chain (`A4Assembly.lean`), hence
`Case2NotA7Impl9` (`NotA7Assembly.lean`), and the whole step-(9) chain
(`Case2NineImpl9_holds` above). -/
theorem case2False_remains2 (I : C4Inputs10)
    (hSetup : Case2SetupImpl9 I.toC4Inputs) (hSix : Case2SixImpl9 I.toC4Inputs)
    (hSeven : Case2SevenImpl I.toC4Inputs)
    (hU : Work.CORE4.C15.A7UMinusProp I.toC4Inputs)
    (h5 : Work.CORE4.C15.A7IndexHWeakProp I.toC4Inputs)
    (h6 : Work.CORE4.C15.A7CosetWeakProp I.toC4Inputs)
    (h7 : Work.CORE4.C15.A7SmallIndexWeakProp I.toC4Inputs)
    (hCount : Case2CountImpl I.toC4Inputs) : Case2FalseProp :=
  case2False_of_layer' I.toC4Inputs hSetup hSix hSeven (Work.CORE4.Case2Eight I.toC4Inputs)
    (Work.CORE4.notA7_of_four_leaves I.toC4Inputs hU h5 h6 h7)
    (Case2NineImpl9_holds I)
    (case2CountImpl9_of_count I.toC4Inputs hCount)

end Work.GW2
