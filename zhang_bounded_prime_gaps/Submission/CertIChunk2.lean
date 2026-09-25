import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `2`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_2 : chunkI 2 = (-46673976102394993138978076077856490960404944037045595342277109753813684248530155458418660685606982055566656953901767775619117738786513752157420443699805211354636652403000305104161139794812325016617867047939615341080071057445251603454087088652242696048769761280000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
