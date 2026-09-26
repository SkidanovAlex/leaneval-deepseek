import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R15

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok15_0 : closOK cmT labT15 stabT15 grepT15 [0,1] (List.range 712) = true := by decide +kernel
theorem clos_ok15_1 : closOK cmT labT15 stabT15 grepT15 [2,3] (List.range 712) = true := by decide +kernel
theorem clos_ok15_2 : closOK cmT labT15 stabT15 grepT15 [4,5] (List.range 712) = true := by decide +kernel
theorem clos_ok15_3 : closOK cmT labT15 stabT15 grepT15 [6,7] (List.range 712) = true := by decide +kernel
theorem clos_ok15_4 : closOK cmT labT15 stabT15 grepT15 [8,9] (List.range 712) = true := by decide +kernel
theorem clos_ok15_5 : closOK cmT labT15 stabT15 grepT15 [10,11] (List.range 712) = true := by decide +kernel
theorem clos_ok15_6 : closOK cmT labT15 stabT15 grepT15 [12,13] (List.range 712) = true := by decide +kernel
theorem clos_ok15_7 : closOK cmT labT15 stabT15 grepT15 [14,15] (List.range 712) = true := by decide +kernel

end Submission.PTCert.C
end
