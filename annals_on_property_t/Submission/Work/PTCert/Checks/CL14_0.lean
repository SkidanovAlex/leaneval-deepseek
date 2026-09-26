import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R14

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok14_0 : closOK cmT labT14 stabT14 grepT14 [0] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_1 : closOK cmT labT14 stabT14 grepT14 [1] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_2 : closOK cmT labT14 stabT14 grepT14 [2] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_3 : closOK cmT labT14 stabT14 grepT14 [3] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_4 : closOK cmT labT14 stabT14 grepT14 [4] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_5 : closOK cmT labT14 stabT14 grepT14 [5] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_6 : closOK cmT labT14 stabT14 grepT14 [6] (List.range 1332) = true := by decide +kernel
theorem clos_ok14_7 : closOK cmT labT14 stabT14 grepT14 [7] (List.range 1332) = true := by decide +kernel

end Submission.PTCert.C
end
