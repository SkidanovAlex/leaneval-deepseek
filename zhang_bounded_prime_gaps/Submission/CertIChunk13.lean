import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk11

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `13`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_13 : chunkI 13 = (417657622631557059664746979054337203571114305890630976862171746935348055821906769608425594185035595589131629224798171464335431768995238754390806249831222278839438704465258295031441426258943827327515584345380324945922064229025072087742792972100105140090961920000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
