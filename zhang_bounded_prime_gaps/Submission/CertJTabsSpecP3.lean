import Submission.CertJTabsSpec2
-- Build-order chain only: one `gTab` window module builds at a time.
import Submission.CertJTabsSpecP2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 102 … 135. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `102 … 135`, checked on the window `wWin 102` (see `accPos_wWin`). -/
theorem gTab_spec_3 : (List.range 34).all (fun k => decide
    ((gPosL.getD (102 + k) [] = accPos (wWin 102) (102 + k)) ∧
     (gNegL.getD (102 + k) [] = accNeg (wWin 102) (102 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
