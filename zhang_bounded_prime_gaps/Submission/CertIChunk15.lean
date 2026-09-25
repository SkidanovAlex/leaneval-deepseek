import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk13

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `15`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_15 : chunkI 15 = (740422984269364953872636218884340118301738798093818460201311344043234704792792884343976732652849078933212983026857065699118388948262851636080755058642500967829517256207964758820581248385935987889384572951798906865164084609371738745736327658394573164477677568000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
