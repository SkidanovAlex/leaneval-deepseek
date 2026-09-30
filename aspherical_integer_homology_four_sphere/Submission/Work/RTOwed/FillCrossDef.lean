/-
# The filling charts of `M̂` together with their cross transitions (items 2 and 3)

Items 2 and 3 of the contract are *not* independent: `Work.RTInstance.CrossData` is stated for the
filling chart family actually built (the collar charts crossing the gluing, whose UHS coordinate is
the cusp coordinate of `Work.Cusp.CuspGlueData`), and the smoothness/isometry of the transitions
between a transported fold chart and a collar chart is a statement about *that* family.  For an
arbitrary `Work.RTInstance.FillData` it is false, because the charts are then unconstrained.

This file therefore bundles the two items in one structure, `Work.RTOwed.FillCross`, so that they are
produced together:

* `charts : Work.RTOwed.FillCharts (assemblyOf g)` — the filling charts with their metric layers,
  their transition data and the three layer covers (item 2; `FillCharts.toFillData` then produces the
  `Work.RTInstance.FillData`, the cover of `M̂` being *proved* from the layer covers and the fold
  cover);
* `cross : Work.RTInstance.CrossData (assemblyOf g) (foldDataOf g) charts.toFillData` — the
  transitions between a transported fold chart and a filling chart (item 3), i.e. the fact that near
  the cusped boundary the two families describe the same hyperbolic metric.

`Work.RTOwed.CuspInputs` is then assembled from an inhabitant of `FillCross` together with the
gluing `g`: `fill := F.charts.toFillData (foldDataOf g)`, `cross := F.cross`.
-/
import Mathlib
import Submission.Work.RTOwed.FillCharts
import Submission.Work.RTOwed.Instance

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.RTOwed

open Work.RTInstance

/-- **The filling charts of `M̂` and their cross transitions to the fold charts.**  The two items are
bundled because the cross transitions are isometries only for the concrete collar charts (those
whose coordinate is the cusp coordinate of the gluing datum `D`). -/
structure FillCross (g : GlueHomeo) where
  /-- The filling charts of `M̂` (item 2), with the three layer covers. -/
  charts : Work.RTOwed.FillCharts (assemblyOf g)
  /-- The cross transitions between a transported fold chart and a filling chart (item 3). -/
  cross : CrossData (assemblyOf g) (foldDataOf g)
    (charts.toFillData (foldDataOf g))

end Work.RTOwed
