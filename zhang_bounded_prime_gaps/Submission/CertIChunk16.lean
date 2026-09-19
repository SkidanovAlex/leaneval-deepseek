import Submission.CertChunks
import Submission.CertIChunk15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `16`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_16 : chunkI 16 = (868141356934153141768723939197990170954427367040206554108668938090910035887712834890254102364392116172131220414345536827672779123010912018201305884079781013617400416917553651993729198251081659238038540718363808834939497937013779823693402094279437424982491136000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
