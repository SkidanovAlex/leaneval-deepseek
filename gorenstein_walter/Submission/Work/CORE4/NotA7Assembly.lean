/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the `A₇` elimination with the `A₄` chain discharged

`Work.CORE4.notA7_of_weak` (`Case2NotA7Impl9.lean`) reduces the `A₇` exclusion of Bender p. 226 to
the leaves `A3m` (`A7UMinusProp`), `A5`, `A6`, `A7` (weak forms) plus the `A₄` chain
(`A4a`, `A4s`, `A4b`, `A4c`).  The `A₄` chain is now **proved** in the area
(`A4Assembly.lean`: `A4a2` + `A4s` + `A4b` + `A4c2` via `C15.invNormalFrom_of_parts2`), and
`SixEmbedProp`, A1 (`A7K`) and A2 (`A7V`) are proved too.

This file records the resulting reduction: `Case2NotA7Impl9 I` from the **four** remaining `A₇`
leaves
* `C15.A7UMinusProp` (A3m: the honest conjuncts of A3, without `K = Z(U)`),
* `C15.A7IndexHWeakProp` (A5), `C15.A7CosetWeakProp` (A6), `C15.A7SmallIndexWeakProp` (A7).
-/
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A4Assembly
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.A7K
import Submission.Work.CORE4.A7V

namespace Work.CORE4

open Work.GW2 Subgroup

/-- **The `A₇` exclusion from four leaves.**  `Case2NotA7Impl9 I` (Bender §4, p. 226) follows from
`A7UMinusProp` (A3m), `A7IndexHWeakProp` (A5), `A7CosetWeakProp` (A6) and
`A7SmallIndexWeakProp` (A7); the `A₄` chain, `SixEmbedProp`, A1 and A2 are proved in this area and
are supplied internally. -/
theorem notA7_of_four_leaves (I : C4Inputs) (hU : C15.A7UMinusProp I) (h5 : C15.A7IndexHWeakProp I)
    (h6 : C15.A7CosetWeakProp I) (h7 : C15.A7SmallIndexWeakProp I) : Case2NotA7Impl9 I := by
  intro G _ _ hbc B hcase2 C hplus hseven height
  refine ⟨fun e => ?_⟩
  have hH : Hyp9 G B C := ⟨hbc, hcase2, hplus, hseven, height⟩
  have hA : IsA7Case C.D := ⟨e⟩
  have f1 : A7Facts1 C.D := A7K I G B C hH hA (Case2SixEmbed I G hbc B C)
  have f2 : A7Facts2 B C.D := A7V I G B C hH hA f1
  have hUd : A7UData B C.D := hU G B C hH hA f1 f2
  have hInv : ¬ Case2InvNormal B C.D :=
    C15.invNormalFrom_of_parts2 I (A4a2 I) (A4s) (A4b I) (A4c2 I) G B C hH hA f1 f2 hUd
  have h5' : A7Facts5 B C.D := h5 G B C hH hA f1 f2 hUd.1 hInv
  have hMid : A7Mid B C.D := ⟨hUd, hInv, h5'⟩
  have h6' : A7Facts6 C.D := h6 G B C hH hA f1 f2 hMid
  obtain ⟨hi, hd⟩ := h7 G B C hH hA f1 f2 hMid h6'
  exact coreIndexProp G hbc.simple C.D.M C.D.M_coatom.ne_top 7 (by norm_num) hd hi

end Work.CORE4
