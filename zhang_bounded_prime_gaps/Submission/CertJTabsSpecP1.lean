import Submission.CertJTabsSpec2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 34 … 67. -/

namespace Commons.NumberTheory.MaynardSieve

theorem gTab_spec_1 : (List.range 34).all (fun k => decide
    ((gPosL.getD (34 + k) [] = accPos wTab (34 + k)) ∧
     (gNegL.getD (34 + k) [] = accNeg wTab (34 + k)))) = true := by decide

end Commons.NumberTheory.MaynardSieve
