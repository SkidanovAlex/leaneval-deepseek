import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R16

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok16_0 : closOK cmT labT16 stabT16 grepT16 [0,1] (List.range 682) = true := by decide +kernel
theorem clos_ok16_1 : closOK cmT labT16 stabT16 grepT16 [2,3] (List.range 682) = true := by decide +kernel
theorem clos_ok16_2 : closOK cmT labT16 stabT16 grepT16 [4,5] (List.range 682) = true := by decide +kernel
theorem clos_ok16_3 : closOK cmT labT16 stabT16 grepT16 [6,7] (List.range 682) = true := by decide +kernel
theorem clos_ok16_4 : closOK cmT labT16 stabT16 grepT16 [8,9] (List.range 682) = true := by decide +kernel
theorem clos_ok16_5 : closOK cmT labT16 stabT16 grepT16 [10,11] (List.range 682) = true := by decide +kernel
theorem clos_ok16_6 : closOK cmT labT16 stabT16 grepT16 [12,13] (List.range 682) = true := by decide +kernel
theorem clos_ok16_7 : closOK cmT labT16 stabT16 grepT16 [14,15] (List.range 682) = true := by decide +kernel

end Submission.PTCert.C
end
