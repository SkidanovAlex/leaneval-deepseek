/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA L2F : bridge for the add-on Props (lead requests, `_design_gw/Core2.lean` §G and
`_design_gw/Core10C4.lean`)

Same device as `Submission/Work/L2F/Bridge.lean`, for the Props that the lead added after the
original contract (all proved in `Submission/Work/L2F/Props/`):

* `Work.L2F.Props.L2CentOddCyclic`      ↦ `GW2.L2CentOddCyclicProp`
* `Work.L2F.Props.L2CentInvariant`      ↦ `GW2.L2CentInvariantProp`
* `Work.L2F.Props.L2TorusNormalizer`    ↦ `GW2.L2TorusNormalizerProp`
* `Work.L2F.Props.L2PrimeSubgroupCount` ↦ `GW2.L2PrimeSubgroupCountProp`
* `Work.L2F.Props.L2NormalizesTwoSylow` ↦ `GW2.L2NormalizesTwoSylowProp`
* `Work.L2F.Props.PGL2CommutatorTorus`  ↦ `GW2.PGL2CommutatorTorusProp`  (input of CORE2A `thm26b`)
(`Work.L2F.Props.L2OuterInvolution` proves the `Core10C4` input `L2OuterInvolutionProp`; it is
deliberately NOT imported here so that this bundle has no `Work.AUTL2` dependency.  Import
`Submission.Work.L2F.Props.L2OuterInvolution` directly if you need it -- note that it (like every
file in the `TwoSylow` subtree) must not be imported together with `Work.CORE4.Defs` until the
duplicated `Work.GW2` vocabulary is unified.)
-/
import Submission.Work.L2F.Props.L2CentOddCyclic
import Submission.Work.L2F.Props.L2CentInvariant
import Submission.Work.L2F.Props.L2TorusNormalizer
import Submission.Work.L2F.Props.L2PrimeSubgroupCount
import Submission.Work.L2F.Props.L2NormalizesTwoSylowFree
import Submission.Work.L2F.Props.PGL2CommutatorTorus
import Submission.Work.LEAD.Core2

namespace Work.L2F.GW2Bridge

/-- `Work.L2F.L2CentOddCyclicProp` transported to the blueprint's name. -/
theorem l2CentOddCyclicProp : GW2.L2CentOddCyclicProp :=
  Work.L2F.Props.L2CentOddCyclic

/-- `Work.L2F.L2CentInvariantProp` transported to the blueprint's name. -/
theorem l2CentInvariantProp : GW2.L2CentInvariantProp :=
  Work.L2F.Props.L2CentInvariant

/-- `Work.L2F.L2TorusNormalizerProp` transported to the blueprint's name. -/
theorem l2TorusNormalizerProp : GW2.L2TorusNormalizerProp :=
  Work.L2F.Props.L2TorusNormalizer

/-- `Work.L2F.L2PrimeSubgroupCountProp` transported to the blueprint's name. -/
theorem l2PrimeSubgroupCountProp : GW2.L2PrimeSubgroupCountProp :=
  Work.L2F.Props.L2PrimeSubgroupCount

/-- `Work.L2F.L2NormalizesTwoSylowProp` transported to the blueprint's name.  Proved via
`Props/L2NormalizesTwoSylowFree.lean`, the `Work.AUTL2`-free proof, so that this bundle can be
imported next to `Work.CORE4.Defs`; the older proof in `Props/L2NormalizesTwoSylow.lean` goes
through the `ℙ¹` model of `Props/TwoSylow/Defs` and does depend on `Work.AUTL2`. -/
theorem l2NormalizesTwoSylowProp : GW2.L2NormalizesTwoSylowProp :=
  Work.L2F.Props.L2NormalizesTwoSylowFree

/-- `Work.L2F.PGL2CommutatorTorusProp` transported to the blueprint's name
(the input of `thm26b` in CORE2A). -/
theorem pgl2CommutatorTorusProp : GW2.PGL2CommutatorTorusProp :=
  Work.L2F.Props.PGL2CommutatorTorus

end Work.L2F.GW2Bridge
