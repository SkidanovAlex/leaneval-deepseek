/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N7 is a theorem, given node N6

`Work.ORFinal.OreFieldFrac K G φK` — Linnell's Ore-field statement (I4′b), the *second* field of
the M1 bridge's `Work.ORBridgeLinnell.HughesFreeInput` — is **not** an independent input.  For a
*one-relator* group `G` it is a consequence of node N6 alone:

* `Work.ORFinal.oreFieldFrac_of_divLoc` — `OreFieldFrac K G φK` from
  `Work.ORFinal.DivLoc K G φK` (node N6's form of (I4): every locally indicable subgroup has a
  division closure which is a division ring);
* `Work.ORFinal.hughesFreeInput_of_div` — the same conclusion in the form of the M1 bridge's
  `HughesFreeInput`, i.e. node N5's envelope with only node N6 as input.

The reduction has two ingredients:

1. the child lemma `Work.ORFinal.OreField.oreFieldFrac_of_div`
   (`Submission/Work/ORFinal/OreField/oreFieldFrac_of_div.lean`), which proves `OreFieldFrac` from
   the division-ring property of `D H` for every subgroup `H` that is `IsMulTorsionFree`; and
2. node N4's theorem `Work.ORLocInd.torsionFree_subgroup_locallyIndicable`: in a one-relator
   group, a torsion-free subgroup is locally indicable.  Hence `IsMulTorsionFree H` gives
   `LocallyIndicable H`, and `DivLoc` applies.

Nothing else is used: in particular no `IsMulTorsionFree` hypothesis is left on the one-relator
path, and the Ore-field statement is never assumed.  This is the removal of the field `hOre` from
`Work.ORFinal.FinalInput`.
-/
import Submission.Work.ORFinal.OreField.oreFieldFrac_of_div
import Submission.Work.ORFinal.AnalyticInput

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORFinal

/-- **Node N7 from node N6, for a one-relator group.**  For a one-relator group `G`, the Ore-field
statement of the M1 bridge follows from `DivLoc` alone: a `IsMulTorsionFree` subgroup of a
one-relator group is locally indicable (node N4,
`Work.ORLocInd.torsionFree_subgroup_locallyIndicable`), so node N6's division-ring property of its
division closure applies, and the child lemma `Work.ORFinal.OreField.oreFieldFrac_of_div` converts
that into `OreFieldFrac`. -/
theorem oreFieldFrac_of_divLoc (K : Type u) [Field K] {G : Type v} [Group G] [Countable G]
    (hG : Group.OneRelator G) (φK : K →+* ℂ) (hdiv : DivLoc K G φK) :
    OreFieldFrac K G φK :=
  OreField.oreFieldFrac_of_div K G φK fun H htf => by
    haveI : IsMulTorsionFree ↥H := htf
    exact hdiv H (Work.ORLocInd.torsionFree_subgroup_locallyIndicable hG
      Work.OROneRel.oneRelatorCombinatorics H Work.ORLocInd.IsTorsionFree.of_isMulTorsionFree)

/-- **The M1 bridge's `HughesFreeInput` from node N6 alone**, for a one-relator group: both fields
of `Work.ORBridgeLinnell.HughesFreeInput` are consequences of `DivLoc K G φK` — `div_of_torsionFree`
by node N4 plus node N6, and `ore_field_frac` by `Work.ORFinal.oreFieldFrac_of_divLoc`.

This is `Work.ORFinal.hughesFreeInput_of_divLoc` with its `OreFieldFrac` hypothesis discharged, and
it is the form in which `Work.ORFinal.ringDataDivOf` consumes the analytic input. -/
theorem hughesFreeInput_of_div (K : Type u) [Field K] {G : Type v} [Group G] [Countable G]
    (hG : Group.OneRelator G) (φK : K →+* ℂ) (hdiv : DivLoc K G φK) :
    Work.ORBridgeLinnell.HughesFreeInput K G (Work.ORBridgeLinnell.countableEnvelope G) φK where
  div_of_torsionFree H htf := by
    haveI htf' : IsMulTorsionFree H := htf
    have htf'' : Work.ORLocInd.IsTorsionFree H :=
      Work.ORLocInd.IsTorsionFree.of_isMulTorsionFree
    exact hdiv H (Work.ORLocInd.torsionFree_subgroup_locallyIndicable hG
      Work.OROneRel.oneRelatorCombinatorics H htf'')
  ore_field_frac := oreFieldFrac_of_divLoc K hG φK hdiv

end Work.ORFinal
