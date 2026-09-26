import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R13

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok13_0 : closOK cmT labT13 stabT13 grepT13 [0] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_1 : closOK cmT labT13 stabT13 grepT13 [1] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_2 : closOK cmT labT13 stabT13 grepT13 [2] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_3 : closOK cmT labT13 stabT13 grepT13 [3] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_4 : closOK cmT labT13 stabT13 grepT13 [4] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_5 : closOK cmT labT13 stabT13 grepT13 [5] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_6 : closOK cmT labT13 stabT13 grepT13 [6] (List.range 1332) = true := by decide +kernel
theorem clos_ok13_7 : closOK cmT labT13 stabT13 grepT13 [7] (List.range 1332) = true := by decide +kernel

end Submission.PTCert.C
end
