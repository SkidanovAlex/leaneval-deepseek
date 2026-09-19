import Submission.CertRowFn
import Submission.CertSsumRow14

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! Rows 240 … 255 of the `Ssum` table `ssumTableL`, checked against the packed row DP
by one `decide` (a `List.all` fold, so that no row is retained). -/

namespace Commons.NumberTheory.MaynardSieve

theorem certRows_15 :
    (List.range 16).all (fun j => decide (ssumTableL.getD (240 + j) []
      = ssumRowOf (cSigs.getD (240 + j) cNil))) = true := by
  decide

end Commons.NumberTheory.MaynardSieve
