import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.fold_source_open_dvor
import Submission.Work.FoldInst.foldPsi_continuousOn
import Submission.Work.FoldInst.foldPhi_mk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- **Continuity of the fold-chart value on `M̄`.**

`foldPhi i` is the descent of `foldPsi i` to the quotient `M̄` (evaluated at any lift,
`foldPhi i p = foldPsi i (Quotient.out p)`).  On the source of the chart — the open saturated set
`U = ⋃ r, mk '' Dvor i r` — the two functions agree on lifts: `foldPhi i (mk x) = foldPsi i x` for
`x ∈ ⋃ r, Dvor i r` (`foldPhi_mk`).  Since `mk` is a quotient map (`isQuotientMap_quotient_mk'`),
`ContinuousOn` descends through it on an *open* target (`IsQuotientMap.continuousOn_isOpen_iff`):
the target `U` is open and `mk ⁻¹' U = ⋃ r, Dvor i r` (`fold_source_open_dvor`), and `foldPsi i` is
continuous there (`foldPsi_continuousOn`). -/
theorem foldPhi_continuousOn (i : Fin 98) :
    ContinuousOn (foldPhi i) (⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r) := by
  obtain ⟨hU, hpre⟩ := fold_source_open_dvor i
  rw [Topology.IsQuotientMap.continuousOn_isOpen_iff (isQuotientMap_quotient_mk' (s := setoid)) hU]
  change ContinuousOn (foldPhi i ∘ mk) (mk ⁻¹' ⋃ r, mk '' Dvor i r)
  rw [hpre]
  exact (foldPsi_continuousOn i).congr (fun x hx => foldPhi_mk i hx)

end Work.FoldInst
