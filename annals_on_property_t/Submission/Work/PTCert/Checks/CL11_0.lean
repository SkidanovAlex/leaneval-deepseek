import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R11

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok11_0 : closOK cmT labT11 stabT11 grepT11 [0] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_1 : closOK cmT labT11 stabT11 grepT11 [1] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_2 : closOK cmT labT11 stabT11 grepT11 [2] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_3 : closOK cmT labT11 stabT11 grepT11 [3] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_4 : closOK cmT labT11 stabT11 grepT11 [4] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_5 : closOK cmT labT11 stabT11 grepT11 [5] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_6 : closOK cmT labT11 stabT11 grepT11 [6] (List.range 1332) = true := by decide +kernel
theorem clos_ok11_7 : closOK cmT labT11 stabT11 grepT11 [7] (List.range 1332) = true := by decide +kernel

end Submission.PTCert.C
end
