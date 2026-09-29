import Submission.Work.CNum.Cert.Tab

/-! # `Work.CNum.CertDnA` — series values, range 0–255 -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svDnTab_specA : ∀ k, k ≤ 255 → svDn (ptOf k) = svDnTab k := by
  intro k hk
  interval_cases k <;> decide +kernel

end Work.CNum
