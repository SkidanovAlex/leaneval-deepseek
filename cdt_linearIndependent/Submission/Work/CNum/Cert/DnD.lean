import Submission.Work.CNum.Cert.Tab

/-! # `Work.CNum.CertDnD` — series values, range 768–1024 -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svDnTab_specD : ∀ k, 768 ≤ k → k ≤ 1024 → svDn (ptOf k) = svDnTab k := by
  intro k h1 h2
  interval_cases k <;> decide +kernel

end Work.CNum
