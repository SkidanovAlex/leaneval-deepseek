import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R17

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok17_0 : closOK cmT labT17 stabT17 grepT17 [0] (List.range 1621) = true := by decide +kernel
theorem clos_ok17_1 : closOK cmT labT17 stabT17 grepT17 [1] (List.range 1621) = true := by decide +kernel
theorem clos_ok17_2 : closOK cmT labT17 stabT17 grepT17 [2] (List.range 1621) = true := by decide +kernel
theorem clos_ok17_3 : closOK cmT labT17 stabT17 grepT17 [3] (List.range 1621) = true := by decide +kernel

end Submission.PTCert.C
end
