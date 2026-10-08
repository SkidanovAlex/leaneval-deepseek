/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the final composition of the §4 elimination

This file records the area's kernel in one place: the leaf statements that the fleet is proving,
composed (through the *proved* assemblies `Core9.lean`/`Core10C4.lean` gave us) into
`Work.GW2.Case2FalseProp`.

* `case2SixImpl9_of_six`, `case2CountImpl9_of_count` — the pass-9 restatements are implied by the
  older, hypothesis-poorer forms of the same leaves (purely mechanical: the pass-9 forms carry
  `Case2PrePlus` / `Case2SevenFacts` / `Case2EightAll` as extra hypotheses).
* `case2False_full` — from the area's leaf layer (Setup9, Six, Seven, Eight, the `A₇` chain
  A1–A8, the step-(9) chain N1–N5d, and Count) to `Case2FalseProp`, with the arithmetic
  (`case2Arith`) discharged internally.

The remaining inputs of `case2False_full` are exactly the leaves; as each is proved, its name can
be substituted (`Work.CORE4.A7K`, …).  See `NOTES_CORE4.md` and `NOTES_TO_LEAD.md` for the state of
each leaf, in particular the two that are blocked at the time of writing (`A7U`, `A7InvNormal`).
-/
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Layer

namespace Work.GW2

open Subgroup

/-- The pass-9 form of `Case2Six` follows from the older form (fewer hypotheses). -/
theorem case2SixImpl9_of_six (I : C4Inputs) (h : Case2SixImpl I) : Case2SixImpl9 I :=
  fun G _ _ hbc B D hpre _hplus => h G hbc B D hpre

/-- The pass-9 form of `Case2Count` follows from the older form (fewer hypotheses). -/
theorem case2CountImpl9_of_count (I : C4Inputs) (h : Case2CountImpl I) : Case2CountImpl9 I :=
  fun G _ _ hbc B h2 hctx _hplus _h7 _h8 => h G hbc B h2 hctx

/-- **The composition.**  From the `A₇` chain (A1–A8), the step-(9) chain (N1–N5d), the §4 (6)
embedding `SixEmbedProp`, the pass-9 leaves `Setup9`, `Seven`, `Eight`, the §4 (6) leaf `Six` and
the counting leaf `Count`, the area delivers `Case2FalseProp`.

`I : C4Inputs10` is `C4Inputs` plus the `L2F` input `l2outer` (`L2OuterInvolutionProp`), which the
N5b leaf `NineR` needs; every other input is taken at `I.toC4Inputs`. -/
theorem case2False_full (I : C4Inputs10)
    (hSetup : Case2SetupImpl9 I.toC4Inputs) (hSix : Case2SixImpl I.toC4Inputs)
    (h0 : SixEmbedProp I.toC4Inputs) (hSeven : Case2SevenImpl I.toC4Inputs)
    (hEight : Case2EightImpl I.toC4Inputs)
    -- the `A₇` chain A1–A8
    (h1 : A7KProp I.toC4Inputs) (h2 : A7VProp I.toC4Inputs) (h3 : A7UProp I.toC4Inputs)
    (h4 : A7InvNormalProp I.toC4Inputs) (h5 : A7IndexHProp I.toC4Inputs)
    (h6 : A7CosetProp I.toC4Inputs) (h7 : A7SmallIndexProp I.toC4Inputs) (h8 : CoreIndexProp)
    -- the step-(9) chain N1–N5d
    (hS : NineShapeProp I.toC4Inputs) (hK : NineKProp I.toC4Inputs)
    (hZ : NineCenterProp I.toC4Inputs) (hO : NineOuterInvProp I.toC4Inputs)
    (hR : NineRProp I.toC4Inputs) (hC : NineConjProp I.toC4Inputs) (hY : NineRyProp I.toC4Inputs)
    -- the counting
    (hCount : Case2CountImpl I.toC4Inputs) : Case2FalseProp :=
  case2False_of_layer' I.toC4Inputs hSetup (case2SixImpl9_of_six _ hSix) hSeven hEight
    (notA7_of_leaves _ h0 h1 h2 h3 h4 h5 h6 h7 h8)
    (nine_of_leaves _ h0 hS hK hZ hO hR hC hY)
    (case2CountImpl9_of_count _ hCount)

end Work.GW2
