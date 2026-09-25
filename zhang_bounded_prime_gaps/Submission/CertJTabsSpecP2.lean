import Submission.CertJTabsSpec2
-- Build-order chain only: one `gTab` window module builds at a time.
import Submission.CertJTabsSpecP1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 68 … 101. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `68 … 101`, checked on the window `wWin 68` (see `accPos_wWin`). -/
theorem gTab_spec_2 : (List.range 34).all (fun k => decide
    ((gPosL.getD (68 + k) [] = accPos (wWin 68) (68 + k)) ∧
     (gNegL.getD (68 + k) [] = accNeg (wWin 68) (68 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
