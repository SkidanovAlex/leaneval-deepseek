import Submission.CertChunks
-- Build-order chain only: at most 2 `I` chunks build at once.
import Submission.CertIChunk7

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `9`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_9 : chunkI 9 = (-2716643180245949996342391509711222759375533266526326500577166658930837285102747502826628667781646410029734898909389559026034629212842234761170627627162948145385123610279009928375057537524479632284097892881486328457507791768300889279236036416480613141860843520000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
