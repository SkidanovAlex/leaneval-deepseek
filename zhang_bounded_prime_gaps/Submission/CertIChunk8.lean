import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk6

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `8`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_8 : chunkI 8 = (19904283775033734467374586461533009364293814136480150025435630835059069985106992959124446819944769548870167301928164156376972642756729739999887242060248116125382874813749788999296568143502074197775243992515087669305872349320653635448695371537592164661988425728000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
