import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `3`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_3 : chunkI 3 = (53778491672587459534955635925586344054042744055316294936317703714213762654247176455033165017993576670203034757190891674152835268811105797903696999857437894371653004394887881048765579713371622028450052681359958966724698417045111336886987884689069395835575336960000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
