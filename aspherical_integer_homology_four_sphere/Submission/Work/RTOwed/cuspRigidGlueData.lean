/-
# The rigidity of the concrete cusp chart of `M̄`

All three fields of `Work.RTOwed.CuspRigid` are now proved for the concrete chart
`Work.RTOwed.mbarLow` and the concrete gluing `Work.RTOwed.glueData`:

* **(F1)** `periodic`  — `Work.RTOwed.mbarLow_periodic`;
* **(F2)** `fibre`     — `Work.RTOwed.mbarLow_fibre`;
* **(F3)** `foldLocal` — `Work.RTOwed.mbarLow_foldLocal`.

This is the input that the cross transitions of the atlas of `M̂` (item 3 of the contract) need, and
which the qualitative interface `Work.Cusp.CuspGlueData` alone does not provide.
-/
import Mathlib
import Submission.Work.RTOwed.cuspGlueDataConcrete
import Submission.Work.RTOwed.mbarLow_periodic
import Submission.Work.RTOwed.mbarLow_fibre
import Submission.Work.RTOwed.mbarLow_foldLocal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.RTInstance

/-- **The rigidity of the `v`-th cusp chart of `M̄`, unconditionally.** -/
theorem cuspRigid_glueData (v : Fin 5) :
    Work.RTOwed.CuspRigid Work.RTOwed.glueData v (Work.RTOwed.cuspGlueData v) where
  periodic := fun (q : Work.Cusp.E4) (L : Work.Cusp.E3) (hL : latVec v L) =>
    mbarLow_periodic v q L hL
  fibre := fun {q q' : Work.Cusp.E4} (h11 : 11 / 10 ≤ q 3)
      (hc : q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)) (h11' : 11 / 10 ≤ q' 3)
      (hc' : q' 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q'))
      (h : mbarLow v q = mbarLow v q') => mbarLow_fibre h11 hc h11' hc' h
  foldLocal := fun (i : Fin 98) {q : Work.Cusp.E4} (h1 : 11 / 10 < q 3)
      (h2 : q 3 < Work.Cusp.beta (Work.Cusp.xOf q))
      (hsrc : mbarLow v q ∈ (Work.FoldInst.foldChart i).source) =>
    mbarLow_foldLocal v i h1 h2 hsrc

end Work.RTOwed
