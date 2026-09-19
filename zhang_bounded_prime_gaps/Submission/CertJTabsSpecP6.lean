import Submission.CertJTabsSpec2
import Submission.CertJTabsSpecP5

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 204 … 237. -/

namespace Commons.NumberTheory.MaynardSieve

theorem gTab_spec_6 : (List.range 34).all (fun k => decide
    ((gPosL.getD (204 + k) [] = accPos wTab (204 + k)) ∧
     (gNegL.getD (204 + k) [] = accNeg wTab (204 + k)))) = true := by decide

end Commons.NumberTheory.MaynardSieve
