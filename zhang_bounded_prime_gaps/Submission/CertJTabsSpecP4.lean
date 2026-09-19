import Submission.CertJTabsSpec2
import Submission.CertJTabsSpecP3

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The group-table accumulation spec, positions 136 … 169. -/

namespace Commons.NumberTheory.MaynardSieve

theorem gTab_spec_4 : (List.range 34).all (fun k => decide
    ((gPosL.getD (136 + k) [] = accPos wTab (136 + k)) ∧
     (gNegL.getD (136 + k) [] = accNeg wTab (136 + k)))) = true := by decide

end Commons.NumberTheory.MaynardSieve
