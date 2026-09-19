import Submission.CertJTabsSpec2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 170 … 203. -/

namespace Commons.NumberTheory.MaynardSieve

theorem gTab_spec_5 : (List.range 34).all (fun k => decide
    ((gPosL.getD (170 + k) [] = accPos wTab (170 + k)) ∧
     (gNegL.getD (170 + k) [] = accNeg wTab (170 + k)))) = true := by decide

end Commons.NumberTheory.MaynardSieve
