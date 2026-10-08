/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA L2F : bridge to the `GW2` Prop names of the blueprint

`Submission/Work/_design_gw/Contracts2.lean` (namespace `GW2`) states the area Props that the
CORE areas consume.  The statements there are *identical* to the ones proved in
`Submission/Work/L2F/` (whose copies live in `Work.L2F.Defs`), up to the unfolding of
`IsFourGroup`; this file records that, so that a caller who has `Contracts2` imported can use

* `Work.L2F.GW2Bridge.l2SylowDihedralProp : GW2.L2SylowDihedralProp`,
* `Work.L2F.GW2Bridge.l2InvolutionCentralizerProp : GW2.L2InvolutionCentralizerProp`,
* `Work.L2F.GW2Bridge.l2FourGroupProp : GW2.L2FourGroupProp`,
* `Work.L2F.GW2Bridge.l2TIProp : GW2.L2TIProp`

together with the six add-on Props of `_design_gw/Core2.lean` §G.
-/
import Submission.Work.L2F.Main
import Submission.Work.LEAD.Contracts2
import Submission.Work.LEAD.Core2

open scoped MatrixGroups

namespace Work.L2F.GW2Bridge

/-- `Work.L2F.L2SylowDihedralProp` transported to the blueprint's name. -/
theorem l2SylowDihedralProp : GW2.L2SylowDihedralProp :=
  Work.L2F.l2SylowDihedral

/-- `Work.L2F.L2InvolutionCentralizerProp` transported to the blueprint's name. -/
theorem l2InvolutionCentralizerProp : GW2.L2InvolutionCentralizerProp :=
  Work.L2F.l2InvolutionCentralizer

/-- `Work.L2F.L2FourGroupProp` transported to the blueprint's name. -/
theorem l2FourGroupProp : GW2.L2FourGroupProp :=
  Work.L2F.l2FourGroup

/-- `Work.L2F.L2TIProp` transported to the blueprint's name. -/
theorem l2TIProp : GW2.L2TIProp :=
  Work.L2F.l2TI

end Work.L2F.GW2Bridge
