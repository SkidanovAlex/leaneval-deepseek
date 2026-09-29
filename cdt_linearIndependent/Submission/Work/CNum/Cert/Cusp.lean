import Submission.Work.CNum.Cert.Tab

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem svUpCA_spec : svUp ptCuspA = svUpCA := by decide +kernel
theorem svDnCA_spec : svDn ptCuspA = svDnCA := by decide +kernel
theorem svUpCB_spec : svUp ptCuspB = svUpCB := by decide +kernel
theorem svDnCB_spec : svDn ptCuspB = svDnCB := by decide +kernel

end Work.CNum
