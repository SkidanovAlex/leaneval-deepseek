/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Area BSW: the finished assembly

This file collects the unconditional case results of Bender's proof — `|K| = 2`, `|K| = 4` and the
Zassenhaus conversion of Bender's conclusion (`Work.BSW.BSWDataZassProp`):

```
Work.BSW.bswK2Prop  : BSWK2Prop
Work.BSW.bswK4Prop  : BSWK4Prop
```

and reduces the assembly of `Work.GW2.BSWZass2Prop` / `Work.GW2.BSW2Prop` to the single remaining
input, Bender §3 (`Work.BSW.BSWCompletionProp`):

```
Work.BSW.bswGt4Prop_of_completion  : BSWCompletionProp → BSWGt4Prop
Work.BSW.bswZass2Prop_of_gt4       : BSWGt4Prop → BSWDataZassProp → BSWZass2Prop
Work.BSW.bswZass2Prop_of_completion : BSWCompletionProp → BSWZass2Prop
Work.BSW.bsw2_of_completion        : BSWCompletionProp → ZassOdd2Prop → BSW2Prop
Work.BSW.bsw2_final                : BSWCompletionProp → BSWDataZassProp → ZassOdd2Prop → BSW2Prop
```

Once `Cases/bswCompletionProp` is clean, `Work.BSW.bswZass2Prop` and `Work.BSW.bsw2_unconditional`
at the end of this file discharge that hypothesis (they are kept commented until then, so that this
file never depends on an unfinished module).
-/
import Submission.Work.BSW.Main
import Submission.Work.BSW.Parity.bswParityProp
import Submission.Work.BSW.Cases.bswOrderProp
import Submission.Work.BSW.Cases.bswK2OrderProp
import Submission.Work.BSW.Cases.bswK2StructureProp2
import Submission.Work.BSW.Cases.bswK4OrderProp
import Submission.Work.BSW.Cases.bswK4StructureProp
import Submission.Work.BSW.Cases.bswDataZassProp
import Submission.Work.BSW.S3.bswCompletionProp_of_leaves

namespace Work.BSW

open Work.GW2

/-- The `|K| = 2` case: `G` satisfies Bender's conclusion with `q = 5`. -/
theorem bswK2Prop : BSWK2Prop :=
  bswK2Prop_of_parts Cases.bswK2OrderProp Cases.bswK2StructureProp2

/-- The `|K| = 4` case: `G` satisfies Bender's conclusion with `q = 7` or `q = 9`. -/
theorem bswK4Prop : BSWK4Prop :=
  bswK4Prop_of_parts Cases.bswK4OrderProp Cases.bswK4StructureProp

/-- The `|K| > 4` case from Bender §3 (`Work.BSW.BSWCompletionProp`). -/
theorem bswGt4Prop_of_completion (hcomp : BSWCompletionProp) : BSWGt4Prop :=
  bswGt4Prop_of_parts Cases.bswOrderProp hcomp

/-- `BSWZass2Prop` from the `|K| > 4` case and the Zassenhaus conversion. -/
theorem bswZass2Prop_of_gt4 (hgt : BSWGt4Prop) (hdata : BSWDataZassProp) : BSWZass2Prop :=
  bswZass2_of_cases Parity.bswParityProp bswK2Prop bswK4Prop hgt hdata

/-- `BSWZass2Prop` from the `|K| > 4` case alone: the Zassenhaus conversion
(`Work.BSW.BSWDataZassProp`) is now unconditional. -/
theorem bswZass2Prop_of_completion (hcomp : BSWCompletionProp) : BSWZass2Prop :=
  bswZass2Prop_of_gt4 (bswGt4Prop_of_completion hcomp) Cases.bswDataZassProp

/-- The deliverable `Work.GW2.BSW2Prop`, from the two Bender §3 inputs and ZASS's Zassenhaus
recognition step. -/
theorem bsw2_final (hcomp : BSWCompletionProp) (hdata : BSWDataZassProp)
    (hZ : ZassOdd2Prop) : BSW2Prop :=
  bsw2 (bswZass2Prop_of_gt4 (bswGt4Prop_of_completion hcomp) hdata) hZ

/-- The deliverable `Work.GW2.BSW2Prop`, from Bender §3 and ZASS's Zassenhaus recognition step. -/
theorem bsw2_of_completion (hcomp : BSWCompletionProp) (hZ : ZassOdd2Prop) : BSW2Prop :=
  bsw2 (bswZass2Prop_of_completion hcomp) hZ

/-- **`Work.BSW.BSWZass2Prop`, unconditional**: Bender's recognition step is complete. -/
theorem bswZass2Prop : BSWZass2Prop :=
  bswZass2Prop_of_completion S3.bswCompletionProp

/-- **The deliverable**, unconditional apart from ZASS's Zassenhaus recognition step
(`Work.GW2.ZassOdd2Prop`): `G ≃ PSL(2, q)`. -/
theorem bsw2_unconditional (hZ : ZassOdd2Prop) : BSW2Prop :=
  bsw2_of_completion S3.bswCompletionProp hZ

end Work.BSW

namespace Work.GW2

/-- Alias of `Work.BSW.bswK2Prop` in the contract namespace. -/
theorem bswK2Prop : Work.BSW.BSWK2Prop := Work.BSW.bswK2Prop

/-- Alias of `Work.BSW.bswK4Prop` in the contract namespace. -/
theorem bswK4Prop : Work.BSW.BSWK4Prop := Work.BSW.bswK4Prop

/-- Alias of `Work.BSW.bswZass2Prop_of_completion` in the contract namespace. -/
theorem bswZass2Prop_of_completion (hcomp : Work.BSW.BSWCompletionProp) :
    BSWZass2Prop := Work.BSW.bswZass2Prop_of_completion hcomp

/-- Alias of `Work.BSW.bsw2_of_completion` in the contract namespace. -/
theorem bsw2_of_completion (hcomp : Work.BSW.BSWCompletionProp) (hZ : ZassOdd2Prop) :
    BSW2Prop := Work.BSW.bsw2_of_completion hcomp hZ

/-- **`Work.GW2.BSWZass2Prop`, unconditional** (alias of `Work.BSW.bswZass2Prop`). -/
theorem bswZass2Prop : BSWZass2Prop := Work.BSW.bswZass2Prop

/-- **The deliverable, unconditional apart from ZASS's `Work.GW2.ZassOdd2Prop`** (alias of
`Work.BSW.bsw2_unconditional`). -/
theorem bsw2_unconditional (hZ : ZassOdd2Prop) : BSW2Prop := Work.BSW.bsw2_unconditional hZ

end Work.GW2
