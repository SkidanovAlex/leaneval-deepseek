import Submission.CertChunks
import Submission.CertIChunk1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `10`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_10 : chunkI 10 = (-4659526194600132851709471341253316780200136243004946645893707455613034695566981743278525816325331931530282476788130213201774824595790273546233255852053695805787357813220549477102801270085245289339779153860476208668368648673415512501957912875933833637427937280000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
