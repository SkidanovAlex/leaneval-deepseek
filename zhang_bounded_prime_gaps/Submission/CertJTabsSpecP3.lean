import Submission.CertJTabsSpec2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 102 … 135. -/

namespace Commons.NumberTheory.MaynardSieve

theorem gTab_spec_3 : (List.range 34).all (fun k => decide
    ((gPosL.getD (102 + k) [] = accPos wTab (102 + k)) ∧
     (gNegL.getD (102 + k) [] = accNeg wTab (102 + k)))) = true := by decide

end Commons.NumberTheory.MaynardSieve
