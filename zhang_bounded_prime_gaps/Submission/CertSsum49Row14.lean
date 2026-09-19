import Submission.CertRowFn49
import Submission.CertSsum49Row13

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! Rows 224 … 239 of the `k = 49` table `ssumTable49L`, checked against the packed row
DP by one `decide` (a `List.all` fold, so that no row is retained). -/

namespace Commons.NumberTheory.MaynardSieve

theorem certRows49_14 :
    (List.range 16).all (fun j => decide (ssumTable49L.getD (224 + j) []
      = ssumRowOfAt 49 (cSigs.getD (224 + j) ([], [])))) = true := by
  decide

end Commons.NumberTheory.MaynardSieve
