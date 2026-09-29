import Submission.Work.CNum.Cert.Tab

/-! # `Work.CNum.CertUpB` — series values, range 256–511 -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svUpTab_specB : ∀ k, 256 ≤ k → k ≤ 511 → svUp (ptOf k) = svUpTab k := by
  intro k h1 h2
  interval_cases k <;> decide +kernel

end Work.CNum
