/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Defs
import Submission.Work.GLUE.pCore_eq_opCore
import Submission.Work.GLUE.piCore_eq_oPiCore
import Submission.Work.GLUE.oddCore_eq_oPiCore
import Submission.Work.GLUE.fitting_eq_isaacsFitting
import Submission.Work.GLUE.isHallIn_iff_isHallSubgroup

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: the definition bridges, re-exported under `Work.GW2`

The four bridge lemmas

* `pCore_eq_opCore`, `piCore_eq_oPiCore`, `oddCore_eq_oPiCore`, `fitting_eq_isaacsFitting`

are proved (by colleagues of this area) in the neighbouring modules
`Submission.Work.GLUE.{pCore_eq_opCore,piCore_eq_oPiCore,oddCore_eq_oPiCore,fitting_eq_isaacsFitting}`
in namespace `Work.GLUE`, because the area's definitions themselves live in namespace
`Work.GW2` (they are the verbatim contract vocabulary of
`Submission/Work/_design_gw/Contracts2.lean`).  This file re-exports them under the area's
own namespace, so that `Work.GW2.X` is the single public interface of the GLUE area and of
the vocabulary it bridges.

Notation used in the odd-order library (`Submission/OddOrder/**`):

* `OddOrder.Isaacs.Ch01.opCore p G = O_p(G)` — the intersection of the Sylow `p`-subgroups,
  i.e. the largest normal `p`-subgroup;
* `OddOrder.Isaacs.Ch03.oPiCore π G = O_π(G)` — the largest normal `π`-subgroup;
* `OddOrder.Isaacs.Ch01.fitting G = F(G) = ⨆_{p prime} O_p(G)`;
* `Subgroup.thompsonJAbelian P = J_a(P)` — the abelian Thompson subgroup.

The group-theoretic content is entirely in the odd-order library; these lemmas are the
*dictionary* between its notation and the contract's.
-/

namespace Work.GW2

/-- `O_p(G)`: our `pCore` (join of the normal `p`-subgroups, wrapped in `normalCore`) is
the library's `opCore` (intersection of the Sylow `p`-subgroups). -/
theorem pCore_eq_opCore {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    pCore p G = OddOrder.Isaacs.Ch01.opCore p G := Work.GLUE.pCore_eq_opCore

/-- `O_π(G)`: our `piCore` is the library's `oPiCore`. -/
theorem piCore_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := Work.GLUE.piCore_eq_oPiCore π

/-- `O(G) = O_{2'}(G)`: our `oddCore` (largest normal subgroup of odd order) is
`O_π(G)` for `π = {2}ᶜ`. -/
theorem oddCore_eq_oPiCore {G : Type*} [Group G] [Finite G] :
    oddCore G = OddOrder.Isaacs.Ch03.oPiCore {q : ℕ | q ≠ 2} G :=
  Work.GLUE.oddCore_eq_oPiCore

/-- `F(G)`: our `fitting` (join of the normal nilpotent subgroups, wrapped in `normalCore`)
is the library's `fitting` (`⨆_{p} O_p(G)`). -/
theorem fitting_eq_isaacsFitting {G : Type*} [Group G] [Finite G] :
    fitting G = OddOrder.Isaacs.Ch01.fitting G := Work.GLUE.fitting_eq_isaacsFitting

/-- A subgroup of a finite group has odd order exactly when it is a `{2}ᶜ`-subgroup. -/
theorem odd_card_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N :=
  Work.GLUE.odd_iff_isPiSubgroup_ne_two N

/-- Our relative Hall-subgroup notion `IsHallIn I K` is the library's (Isaacs)
`IsHallSubgroup` for the pair `(primesOf I, I.subgroupOf K)`. -/
theorem isHallIn_iff_isHallSubgroup {G : Type*} [Group G] [Finite G] {I K : Subgroup G}
    (h : I ≤ K) :
    IsHallIn I K ↔
      OddOrder.Isaacs.Ch03.IsHallSubgroup (primesOf I) (I.subgroupOf K) :=
  Work.GLUE.isHallIn_iff_isHallSubgroup h

end Work.GW2
