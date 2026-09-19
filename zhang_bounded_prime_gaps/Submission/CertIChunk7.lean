import Submission.CertChunks
import Submission.CertIChunk6

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `7`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_7 : chunkI 7 = (19223175222424363727231737322155876267127903061713625361066624402973047909538374630756781237125580775334084037225864707288811944790537991938169777517980315674795098091685422063042564723972830346448180290385750072145323370840603068453074416611242779793770414080000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
