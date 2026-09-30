/-
# The fibre form of the boundary compatibility of the cell atlas of `M̄`

The target `mbarBd_fiber` is the statement that for every cell `e` of `M̄` in degree `n + 1` and
every cell `f` in degree `n`, the `(f,e)`-entry of the matrix of `Gen.mbarBd n` is the sum of the
signed incidences `qInc R G * oS (sigVec c G) G` over the facets `G` of the root face `R` of `e`
whose `moCell`-value is the cell `f` (here `c` is the copy bit of the root node, `moCell`/`moRoot`
are the orbit tables of `Data/MbarOrbits.lean` and `qInc`/`oS` are the incidence and sign tables
of `Q̄`).

The proof runs through the sparse vector `gcol n e` of the geometric column (`Defs.lean`), checked
column by column against `imgCol n e` (the column of `mbarBd n` read in the cell numbering) by the
`decide` certificates of `Cols.lean`.  The two halves are glued by the generic bridges
`sum_filter_toFun` (a filtered `Finset.sum` is the coordinate of a sparse vector) and
`toFun_map_inj` (reindexing a sparse vector along the injective `moCid n`), so that no further
computation is needed.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasCocycle
import Submission.Work.MbarHomology.BdFiber.Cols

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

open scoped BigOperators

namespace Work.MbarHomology.BdFiber

open Work.Certificates

theorem mbarBd_fiber (n : ℕ) (hn : n + 1 < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) (f : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    ∑ G ∈ (Work.MbarHomology.qFacet (Work.MbarHomology.Mbar.moRoot (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e))).filter (fun G => Work.MbarHomology.Mbar.moCell (Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e)) G = Work.MbarHomology.Mbar.moCid ⟨n, by omega⟩ f),
      Work.MbarHomology.qInc (Work.MbarHomology.Mbar.moRoot (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e)) G * Work.MbarHomology.oS (Work.MbarHomology.Mbar.sigVec (Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e)) G) G
    = (Work.HomologyIso.Gen.mbarBd n).toMatrix f e := by
  -- the geometric side, as a coordinate of the sparse vector `gcol n e`
  have hbridge : (∑ G ∈ (Work.MbarHomology.qFacet (Work.MbarHomology.Mbar.moRoot (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e))).filter (fun G => Work.MbarHomology.Mbar.moCell (Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e)) G = Work.MbarHomology.Mbar.moCid ⟨n, by omega⟩ f),
      Work.MbarHomology.qInc (Work.MbarHomology.Mbar.moRoot (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e)) G * Work.MbarHomology.oS (Work.MbarHomology.Mbar.sigVec (Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n + 1, hn⟩ e)) G) G)
      = SVec.toFun (gcol n e) (Mbar.moCid ⟨n, by omega⟩ f) := by
    rw [← qFacetL_toFinset (Mbar.moRoot (Mbar.moCid ⟨n + 1, hn⟩ e))]
    rw [sum_filter_toFun (qFacetL (Mbar.moRoot (Mbar.moCid ⟨n + 1, hn⟩ e)))
      (qFacetL_nodup _)
      (fun G => Mbar.moCell (Mbar.moRootC (Mbar.moCid ⟨n + 1, hn⟩ e)) G)
      (fun G => qInc (Mbar.moRoot (Mbar.moCid ⟨n + 1, hn⟩ e)) G *
        oS (Mbar.sigVec (Mbar.moRootC (Mbar.moCid ⟨n + 1, hn⟩ e)) G) G)
      (Mbar.moCid ⟨n, by omega⟩ f)]
    simp only [gcol, dif_pos hn]
  rw [hbridge]
  -- the column check
  rw [colOk_sound (colOk_all n hn e)]
  -- the column of `mbarBd`, reindexed
  rw [show SVec.toFun (imgCol n e) (Mbar.moCid ⟨n, by omega⟩ f)
      = SVec.toFun ((Work.HomologyIso.Gen.mbarBd n).img e) f from ?_]
  · rfl
  · simp only [imgCol, dif_pos hn]
    exact toFun_map_inj (Mbar.moCid ⟨n, by omega⟩) (moCid_injective n (by omega))
      ((Work.HomologyIso.Gen.mbarBd n).img e) f

end Work.MbarHomology.BdFiber
