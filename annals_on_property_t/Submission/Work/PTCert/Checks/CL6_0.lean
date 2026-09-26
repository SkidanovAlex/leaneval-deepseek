import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok6_0 : closOK cmT labT6 stabT6 grepT6 [0,1] (List.range 682) = true := by decide +kernel
theorem clos_ok6_1 : closOK cmT labT6 stabT6 grepT6 [2,3] (List.range 682) = true := by decide +kernel
theorem clos_ok6_2 : closOK cmT labT6 stabT6 grepT6 [4,5] (List.range 682) = true := by decide +kernel
theorem clos_ok6_3 : closOK cmT labT6 stabT6 grepT6 [6,7] (List.range 682) = true := by decide +kernel
theorem clos_ok6_4 : closOK cmT labT6 stabT6 grepT6 [8,9] (List.range 682) = true := by decide +kernel
theorem clos_ok6_5 : closOK cmT labT6 stabT6 grepT6 [10,11] (List.range 682) = true := by decide +kernel
theorem clos_ok6_6 : closOK cmT labT6 stabT6 grepT6 [12,13] (List.range 682) = true := by decide +kernel
theorem clos_ok6_7 : closOK cmT labT6 stabT6 grepT6 [14,15] (List.range 682) = true := by decide +kernel

end Submission.PTCert.C
end
