import Submission.CertChunks
import Submission.CertIChunk4

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `5`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_5 : chunkI 5 = (-56726011869549521778020505785256514078678671344799791705355322342812357960355629063710829608052096274178874102526712716556872128007041505957883788492206067692007032791805189931263396744328433282897241602966335376768908495573091005554919012865228942942618517504000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
