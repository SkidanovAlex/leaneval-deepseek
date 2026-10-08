/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area FUS, `Work.FUS`)

# Area FUS: the two deliverables of the contract, packaged

* `Work.FUS.involutionFusionProp : Work.GW2.InvolutionFusionProp` (file `Fusion.lean`);
* `Work.FUS.centralizerSplitProp : Work.GW2.CentralizerSplitProp` (file `Split.lean`).

A caller building (`a copy of`) `GW2.LocalToolkit` can take

```
import Submission.Work.FUS.Deliverable
...
exact Work.FUS.fus_deliverable
```

for the pair. `Work.GW2.InvolutionFusionProp` and `Work.GW2.CentralizerSplitProp` themselves are
the verbatim copies of the contract statements, in `Submission/Work/FUS/Defs.lean`.
-/
import Submission.Work.FUS.Fusion
import Submission.Work.FUS.Split

namespace Work.FUS

/-- Both FUS deliverables, as a single conjunction. -/
theorem fus_deliverable : Work.GW2.InvolutionFusionProp ∧ Work.GW2.CentralizerSplitProp :=
  ⟨involutionFusionProp, centralizerSplitProp⟩

end Work.FUS
