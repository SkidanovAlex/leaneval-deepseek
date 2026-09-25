import Submission.CertJTabsSpec2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 0 … 33. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Positions `0 … 33`, checked on the window `wWin 0` (see `accPos_wWin`). -/
theorem gTab_spec_0 : (List.range 34).all (fun k => decide
    ((gPosL.getD (0 + k) [] = accPos (wWin 0) (0 + k)) ∧
     (gNegL.getD (0 + k) [] = accNeg (wWin 0) (0 + k)))) = true := by decide +kernel

end Commons.NumberTheory.MaynardSieve
