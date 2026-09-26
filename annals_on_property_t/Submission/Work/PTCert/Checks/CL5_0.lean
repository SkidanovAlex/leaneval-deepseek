import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R5

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok5_0 : closOK cmT labT5 stabT5 grepT5 [0] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_1 : closOK cmT labT5 stabT5 grepT5 [1] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_2 : closOK cmT labT5 stabT5 grepT5 [2] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_3 : closOK cmT labT5 stabT5 grepT5 [3] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_4 : closOK cmT labT5 stabT5 grepT5 [4] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_5 : closOK cmT labT5 stabT5 grepT5 [5] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_6 : closOK cmT labT5 stabT5 grepT5 [6] (List.range 1332) = true := by decide +kernel
theorem clos_ok5_7 : closOK cmT labT5 stabT5 grepT5 [7] (List.range 1332) = true := by decide +kernel

end Submission.PTCert.C
end
