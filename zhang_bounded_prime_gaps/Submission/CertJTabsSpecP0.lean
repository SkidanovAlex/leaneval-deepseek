import Submission.CertJTabsSpec2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 0 … 33. -/

namespace Commons.NumberTheory.MaynardSieve

theorem gTab_spec_0 : (List.range 34).all (fun k => decide
    ((gPosL.getD (0 + k) [] = accPos wTab (0 + k)) ∧
     (gNegL.getD (0 + k) [] = accNeg wTab (0 + k)))) = true := by decide

end Commons.NumberTheory.MaynardSieve
