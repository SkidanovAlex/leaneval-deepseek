import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R12

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok12_0 : closOK cmT labT12 stabT12 grepT12 [0] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_1 : closOK cmT labT12 stabT12 grepT12 [1] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_2 : closOK cmT labT12 stabT12 grepT12 [2] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_3 : closOK cmT labT12 stabT12 grepT12 [3] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_4 : closOK cmT labT12 stabT12 grepT12 [4] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_5 : closOK cmT labT12 stabT12 grepT12 [5] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_6 : closOK cmT labT12 stabT12 grepT12 [6] (List.range 1332) = true := by decide +kernel
theorem clos_ok12_7 : closOK cmT labT12 stabT12 grepT12 [7] (List.range 1332) = true := by decide +kernel

end Submission.PTCert.C
end
