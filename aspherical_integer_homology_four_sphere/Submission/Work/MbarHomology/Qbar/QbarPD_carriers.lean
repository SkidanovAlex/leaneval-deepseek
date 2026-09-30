import Mathlib
import Submission.Work.MbarHomology.Qbar.Basic
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertPat
import Submission.Work.MbarHomology.Qbar.QbarCertSupH
import Submission.Work.MbarHomology.Qbar.QbarCertHadd
import Submission.Work.MbarHomology.Qbar.QbarPD_hemp_of_pattern
import Submission.Work.MbarHomology.Qbar.Carriers_of_sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Qbar

open Work.ConvexCells

/-- **Face completeness of the `865`-face list of `Q̄`** (work package W2 of
`Submission/Work/NOTES_LEAD_eA.md`): every point of `Q̄` lies in the relative interior of exactly
one listed face.

The proof follows the maximality argument of `Work.ConvexCells.Carriers_of_Ok`, with the
`OkEmp`/`OkAdd` certificates of `QbarPD` (which are degenerate: `empSel ≡ true` with zero
certificates) replaced by the sparse Farkas certificates of `Work.MbarHomology.Qbar`:

* for every face `f` and constraint `i` with `empSelB f i = true` the pair is certified empty by
  the `888` patterns of `QbarCertData` (`hpatAll` for the pattern identities, `hsupAll` for the
  support conditions that transfer the pattern certificate to the pair, and
  `QbarPD_hemp_of_pattern` for the transfer itself);
* for every pair with `empSelB f i = false`, the region `Fset f ∩ {i tight}` is the face
  `empAddIdx f i = qOfCode (qCode (qTight f ∪ {i}))`, whose tight set is exactly `qTight f ∪ {i}`
  (`haddAll`).

The emptiness patterns and the support data were generated and verified exactly (in integers and
rationals) by `_w2_gen3.py`; the decidable checks are `hpatAll`, `hsupAll`, `haddAll`. -/
theorem QbarPD_carriers : Work.ConvexCells.PolytopeData.Carriers Work.MbarHomology.QbarPD :=
  Work.MbarHomology.Qbar.Carriers_of_sparse Work.MbarHomology.QbarPD
    Work.MbarHomology.QbarPD_okBasic
    Work.MbarHomology.empSelB Work.MbarHomology.empMu Work.MbarHomology.empMuI
    Work.MbarHomology.empLamIdx Work.MbarHomology.empLamVal Work.MbarHomology.empAddIdx
    (Work.MbarHomology.Qbar.QbarPD_hemp_of_pattern Work.MbarHomology.hpatAll
      Work.MbarHomology.hsupAll)
    (fun f i h => Work.MbarHomology.haddAll f i h)

end Work.MbarHomology.Qbar
