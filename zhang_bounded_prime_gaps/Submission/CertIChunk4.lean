import Submission.CertChunks
import Submission.CertIChunk3

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `4`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_4 : chunkI 4 = (3269237392207528276423525490839705950848064962499198200120090001727780035343442644664935501743589158571285683212806692034976625683785990975719372658706767230181097106384523679948208366307370152247282384656487370281212242636353819326355830550716504947598295040000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
