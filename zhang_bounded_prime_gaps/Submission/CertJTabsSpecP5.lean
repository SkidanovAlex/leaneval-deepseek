import Submission.CertJTabsSpec2
-- Build-order chain only: one `gTab` window module builds at a time.
import Submission.CertJTabsSpecP4

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 170 … 203. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `170 … 203`, checked on the window `wWin 170` (see `accPos_wWin`). -/
theorem gTab_spec_5 : (List.range 34).all (fun k => decide
    ((gPosL.getD (170 + k) [] = accPos (wWin 170) (170 + k)) ∧
     (gNegL.getD (170 + k) [] = accNeg (wWin 170) (170 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
