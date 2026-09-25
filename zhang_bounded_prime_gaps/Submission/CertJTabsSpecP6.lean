import Submission.CertJTabsSpec2
-- Build-order chain only: one `gTab` window module builds at a time.
import Submission.CertJTabsSpecP5

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 204 … 237. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `204 … 237`, checked on the window `wWin 204` (see `accPos_wWin`). -/
theorem gTab_spec_6 : (List.range 34).all (fun k => decide
    ((gPosL.getD (204 + k) [] = accPos (wWin 204) (204 + k)) ∧
     (gNegL.getD (204 + k) [] = accNeg (wWin 204) (204 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
