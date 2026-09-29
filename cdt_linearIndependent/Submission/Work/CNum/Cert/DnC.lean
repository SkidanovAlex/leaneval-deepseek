import Submission.Work.CNum.Cert.Tab

/-! # `Work.CNum.CertDnC` — series values, range 512–767 -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svDnTab_specC : ∀ k, 512 ≤ k → k ≤ 767 → svDn (ptOf k) = svDnTab k := by
  intro k h1 h2
  interval_cases k <;> decide +kernel

end Work.CNum
