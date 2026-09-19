import Submission.CertChunks
import Submission.CertIChunk10

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `11`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_11 : chunkI 11 = (-8366438852043954744083958810500531967303162815688680243577680271251372691036508847823762860598489312064415086711245261437104955707282746873548912191682616117263330455566161787092693519151460340406697141967673690566438852500061898901160162698547530546075297382400 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
