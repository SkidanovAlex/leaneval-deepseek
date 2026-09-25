import Submission.CertJTabsSpec2
-- Build-order chain only: one `gTab` window module builds at a time.
import Submission.CertJTabsSpecP6

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 238 … 271. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `238 … 271`, checked on the window `wWin 238` (see `accPos_wWin`). -/
theorem gTab_spec_7 : (List.range 34).all (fun k => decide
    ((gPosL.getD (238 + k) [] = accPos (wWin 238) (238 + k)) ∧
     (gNegL.getD (238 + k) [] = accNeg (wWin 238) (238 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
