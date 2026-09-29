import Submission.Work.CNum.Cert.Tab

/-! # `Work.CNum.CertUpA` — series values, range 0–255 -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svUpTab_specA : ∀ k, k ≤ 255 → svUp (ptOf k) = svUpTab k := by
  intro k hk
  interval_cases k <;> decide +kernel

end Work.CNum
