/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.OddOrder.FeitThompson
import Submission.OddOrder.GroupTheory.GlaubermanZJ
import Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian
import Submission.OddOrder.GroupTheory.OpResidual
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Basic
import Submission.Work.ASM.Defs

/-!
# GLUE: the vocabulary of the Gorenstein–Walter development

Every definition in `Submission/Work/_design_gw/Contracts2.lean` (the area contract file,
namespace `GW2`) is reproduced here **verbatim**, in namespace `Work.GW2`, so that the GLUE
area is self-contained and so that `Work.GW2.X` is definitionally equal to `GW2.X` for every
definition `X` of the contract file.  Consequently an inhabitant of `Work.GW2.ZJAProp` is
accepted by `exact` where `GW2.ZJAProp` is expected, and conversely.

The **whole point** of this area is that the vocabulary above is *our* notation for objects
that the (third-party, do-not-edit) odd-order library `Submission/OddOrder/**` already
defines under its own names.  This file fixes the notation; the file `Bridge.lean` proves
that the notations agree:

* `Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G`          (`pCore_eq_opCore`)
* `Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G`        (`piCore_eq_oPiCore`)
* `Work.GW2.oddCore G  = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ 2} G`
* `Work.GW2.fitting G  = OddOrder.Isaacs.Ch01.fitting G`           (`fitting_eq_isaacsFitting`)
* `Work.GW2.thompsonJ P = Subgroup.thompsonJAbelian P`             (`thompsonJ_eq_thompsonJAbelian`)
* `Work.GW2.IsPStable' p X ↔ Subgroup.IsPStableOp p X`             (`IsPStable'_iff_IsPStableOp`)

and the file `ZjA.lean` proves the area deliverable

* `Work.GW2.zjA (hPS : PStableProp) : ZJAProp`

(Glauberman's `Z(J)`-theorem, Theorem A, in our terms) from the library theorem
`Subgroup.zCenter_thompsonJAbelian_normal`.

Conventions (copied from the contract file): subgroups of an ambient `G` are used
throughout; `…In K` is the corresponding subgroup of `↥K`, mapped into `G`; every area
theorem has the shape `inputs (other areas' Props) → own Prop`, and an area never assumes
its own deliverable.
-/

open scoped MatrixGroups

namespace Work.GW2
open Subgroup

/-! ## 0. Vocabulary -/

section Vocabulary

variable {G : Type*} [Group G]


end Vocabulary

/-! ## 1. D-groups and the global statements -/


/-! ## 2. Bender's minimal-counterexample context -/


namespace BenderSetup
variable {G : Type} [Group G] [Finite G] (B : BenderSetup G)
end BenderSetup


/-! ## 3. Area deliverables (Props) -/

/-! ### FUS: dihedral fusion (Gorenstein 7.7) -/


/-! ### COPR: Bender 1.1, 1.3, 1.5 (coprime action; FT-free since `P` is a `p`-group) -/


/-! ### DSTR: D-group structure (Bender 1.6, 1.9, 1.10) -/


/-! ### AUTL2 / AUTA7: almost-simple overgroups with dihedral Sylow 2-subgroups -/


/-! ### L2F / A7F: model facts. These are the initial lists. CORE owners request more facts
through the lead, stated on the concrete models. -/


/-! ### BMAX: Bender 1970 1.6/1.7 = Bender 1981 Lemma 2.3 -/


/-! ### ZJ: Glauberman 1968, Theorems A and B, for groups with dihedral/cyclic Sylow 2 -/


/-! ### BG: Bender–Glauberman 1981, Theorems A, B, C -/


namespace BGData
variable {G : Type} [Group G] [Finite G] (D : BGData G)
end BGData


/-! ### BSW / ZASS / A7REC: recognition -/


/-! ### CORE2A: Bender Lemmas 2.1, 2.2, 2.4, 2.5 and Theorem 2.6 -/


/-! ### CORE2B: Bender Lemmas 2.7–2.9 and Theorem 2.10 -/


/-! ### CORE3 / CORE4: elimination of the two cases -/


/-! ## 4. Bundles: the shared local toolkit consumed by the CORE areas -/


end Work.GW2
