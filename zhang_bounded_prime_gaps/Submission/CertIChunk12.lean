import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk10

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `12`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_12 : chunkI 12 = (-585755557140840649066134050849520927387195822999211317499975804996349934103890738723815857172881850704622076966416122205927653818791071196978927955526943779097619254059075368553921011765585470334048694218377277396335346584719396943825180254372505227754471424000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
