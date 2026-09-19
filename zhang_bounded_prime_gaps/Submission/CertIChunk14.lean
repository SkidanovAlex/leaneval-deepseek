import Submission.CertChunks
import Submission.CertIChunk13

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `14`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_14 : chunkI 14 = (544985251974043518746672459061566763343413627334536900468192235466017239481350604923888592191524540273774580476179314983707960571093114634982110899918481986981900141473155369428420927098701361257397626224196752786005181250180996613351433192650815658335928320000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
