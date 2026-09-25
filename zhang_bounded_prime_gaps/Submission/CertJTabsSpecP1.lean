import Submission.CertJTabsSpec2
-- Build-order chain only: one `gTab` window module builds at a time.
import Submission.CertJTabsSpecP0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 34 … 67. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `34 … 67`, checked on the window `wWin 34` (see `accPos_wWin`). -/
theorem gTab_spec_1 : (List.range 34).all (fun k => decide
    ((gPosL.getD (34 + k) [] = accPos (wWin 34) (34 + k)) ∧
     (gNegL.getD (34 + k) [] = accNeg (wWin 34) (34 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
