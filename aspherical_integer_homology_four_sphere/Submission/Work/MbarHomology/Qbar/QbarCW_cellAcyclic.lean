import Mathlib
import Submission.Work.MbarHomology.Qbar.CW
import Submission.Work.MbarHomology.Local.CellLe
import Submission.Work.MbarHomology.Qbar.QbarCxAll

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.Qbar

/-- **Every closed cell of the face poset of `Q̄` has the homology of a point** (work package W5 of
`Submission/Work/NOTES_LEAD_eA.md`).  The intended proof is one `Work.Certificates.SDR` certificate
per cell (at most `865` cells, and at most `75` for all cells but the top one), exhibiting the
`cellLe QbarCW hdd e` as a retract of the contractible complex with `b = (1,0,…)`; the `SDR`
certificate machinery is in `Submission/Work/Certificates/SDR`.  A uniform generator emitting the
certificates from `qFacet`/`qInc` is the intended route; note that the top cell alone has `865`
cells, so it is worth splitting per degree. -/
theorem QbarCW_cellAcyclic (hdd : Work.Subdivision.PolyCW.HasDdZero Work.MbarHomology.QbarCW) :
    Work.MbarHomology.IsCellAcyclic Work.MbarHomology.QbarCW hdd := by
  intro e k
  have he : e = (⟨e.idx⟩ : QbarCell) := QbarCell.ext rfl
  rw [he]
  exact Work.MbarHomology.QbarCxData.allAcyclic hdd e.idx k

end Work.MbarHomology.Qbar
