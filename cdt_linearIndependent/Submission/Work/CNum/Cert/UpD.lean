import Submission.Work.CNum.Cert.Tab

/-! # `Work.CNum.CertUpD` — series values, range 768–1024 -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svUpTab_specD : ∀ k, 768 ≤ k → k ≤ 1024 → svUp (ptOf k) = svUpTab k := by
  intro k h1 h2
  interval_cases k <;> decide +kernel

end Work.CNum
