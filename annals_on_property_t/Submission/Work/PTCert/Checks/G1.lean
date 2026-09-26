import Submission.Work.PTCert.Data.S0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem pc_ok : eqL allPCk pcL = true := by decide +kernel
theorem pitab_ok : tabsOK piCodes piT = true := by decide +kernel
theorem piitab_ok : tabsOK piICodes piIT = true := by decide +kernel
theorem piinv_ok : piInvOK piT piIT 120 = true := by decide +kernel
theorem ntab_ok : tabsOK nCodes nT = true := by decide +kernel

end Submission.PTCert.C
end
