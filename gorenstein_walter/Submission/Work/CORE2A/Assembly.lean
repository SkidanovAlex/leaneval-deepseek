/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.lemma21
import Submission.Work.CORE2A.lemma22
import Submission.Work.CORE2A.lemma24_rev
import Submission.Work.CORE2A.thm26a_of_lemma22
import Submission.Work.CORE2A.Thm26b
import Submission.Work.CORE2A.c13_thm26bOneClass
import Submission.Work.CORE2A.c14_torus
import Submission.Work.CORE2A.thm26_of_steps
import Submission.Work.CORE2A.thm26c
import Submission.Work.CORE2A.lemma25_of_thm26b

/-!
# CORE2A: the deliverables, assembled

This file composes the proved leaves of the area into the two deliverables of the contract:

* `Work.GW2.Lemma22Prop` — proved as `Work.CORE2A.lemma22` (Bender's Lemma 2.2);
* `Work.GW2.Thm26Prop` — Theorem 2.6, assembled here from
  * step 1 `Work.CORE2A.thm26a_of_lemma22` (`O₂(Ĥ) ≠ 1`),
  * step 2 `Work.CORE2A.thm26b_v14` (`E(Ĥ) = 1`, the design-pass-14 route),
  * step 3 `Work.CORE2A.thm26c` (in flight), `Work.CORE2A.thm26_of_steps`.

## Inputs

The contract's `thm26` takes `(T : LocalToolkit)`, `BGThmBProp`, `BSW2Prop`, `Lemma22Prop`,
`Lemma23Prop`, `ZJAProp`, `ZJBProp`.  Two design changes since `Contracts2.lean`:

* `ZJBProp → ZJBProp'` (design pass 11: the product order the source proves) — see
  `Work.CORE2A.lemma24_rev`;
* Theorem 2.6 step 2 additionally needs the design-pass-14 input
  `hAut : Thm26bAutProp` (the strengthened `PGL₂(q)` recognition, proved as `c14_aut` from
  `Lemma21Prop`, `LayerShapeProp`, `TwoRankProp`, `LayerOneInvClassProp`, `AutL2Prop`,
  `AutA7Prop`) and `hCom : Work.L2F.PGL2CommutatorTorusProp` (the commutator tori of `PGL₂(q)`).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- **Theorem 2.6 step 2** (`E(Ĥ) = 1`), design-pass-14 route: Bender's p. 220 paragraph, whose
crux `Thm26bTorusProp` is `Work.CORE2A.c14_torus`, is turned into `Thm26bOneClassProp` by the
K1–K3 reduction (`Work.CORE2A.c13_thm26bOneClass`), and that contradicts Lemma 2.1. -/
theorem Thm26bOneClassV14 (T : Work.GW2.LocalToolkit) (hAut : Work.GW2.Thm26bAutProp)
    (hCom : Work.L2F.PGL2CommutatorTorusProp) : Work.GW2.Thm26bOneClassProp :=
  c13_thm26bOneClass T (c14_torus T hAut hCom)

/-- **Theorem 2.6 step 2**, `E(Ĥ) = 1`, from the BSW/Theorem-B inputs. -/
theorem thm26b_v14 (T : Work.GW2.LocalToolkit) (hB : Work.GW2.BGThmBProp)
    (hBSW : Work.GW2.BSW2Prop) (hAut : Work.GW2.Thm26bAutProp)
    (hCom : Work.L2F.PGL2CommutatorTorusProp) : Work.GW2.Thm26bProp :=
  thm26b_of_oneClass (lemma21 T hB hBSW) (Thm26bOneClassV14 T hAut hCom)

/-- **Bender's Theorem 2.6**, assembled from the leaves.  `thm26c` is
`Work.CORE2A.thm26c` (design pass 21, `O_p(H^g) = O_p(H)^g`) and Bender's Lemma 2.5 is discharged
by `Work.CORE2A.lemma25_of_thm26b` (design pass 22: 2.3 + 2.4 + `Thm26bProp`), so the contract's
sentence is complete. -/
theorem thm26_modulo (T : Work.GW2.LocalToolkit) (hB : Work.GW2.BGThmBProp)
    (hBSW : Work.GW2.BSW2Prop) (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop)
    (hZA : Work.GW2.ZJAProp)
    (hZB : Work.GW2.ZJBProp') (hAut : Work.GW2.Thm26bAutProp)
    (hCom : Work.L2F.PGL2CommutatorTorusProp) : Work.GW2.Thm26Prop :=
  thm26_of_steps T
    (thm26a_of_lemma22 T (lemma21 T hB hBSW) h22 h23 (lemma24_rev T hZA hZB)
      (lemma25_of_thm26b h23 (lemma24_rev T hZA hZB) (thm26b_v14 T hB hBSW hAut hCom)))
    (thm26b_v14 T hB hBSW hAut hCom)
    (thm26c T (lemma21 T hB hBSW) h23 (lemma24_rev T hZA hZB)
      (lemma25_of_thm26b h23 (lemma24_rev T hZA hZB) (thm26b_v14 T hB hBSW hAut hCom)))

/-- **Bender's Theorem 2.6** in the contract's shape. -/
theorem thm26 (T : Work.GW2.LocalToolkit) (hB : Work.GW2.BGThmBProp) (hBSW : Work.GW2.BSW2Prop)
    (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop)
    (hZA : Work.GW2.ZJAProp) (hZB : Work.GW2.ZJBProp') (hAut : Work.GW2.Thm26bAutProp)
    (hCom : Work.L2F.PGL2CommutatorTorusProp) : Work.GW2.Thm26Prop :=
  thm26_modulo T hB hBSW h22 h23 hZA hZB hAut hCom

end Work.CORE2A

/-! ## Contract names

The contract file `_design_gw/Contracts2.lean` states the area's theorems in namespace `GW2`; the
proved versions live in `Work.CORE2A`.  The aliases below make the contract names available
verbatim, so that a caller written against `Contracts2.lean` type-checks unchanged. -/

namespace Work.GW2

/-- `Contracts2.lean`'s `lemma22`: Bender's Lemma 2.2. -/
theorem lemma22 (T : LocalToolkit) (hC : BGThmCProp) (hBSW : BSW2Prop) : Lemma22Prop :=
  Work.CORE2A.lemma22 T hC hBSW

/-- `Contracts2.lean`'s `lemma23`-style leaf: Bender's Lemma 2.1. -/
theorem lemma21 (T : LocalToolkit) (hB : BGThmBProp) (hBSW : BSW2Prop) : Lemma21Prop :=
  Work.CORE2A.lemma21 T hB hBSW

/-- Bender's Lemma 2.4 in the product order of design pass 11 (`ZJBProp'`). -/
theorem lemma24_rev (T : LocalToolkit) (hZA : ZJAProp) (hZB : ZJBProp') : Lemma24Prop :=
  Work.CORE2A.lemma24_rev T hZA hZB

end Work.GW2
