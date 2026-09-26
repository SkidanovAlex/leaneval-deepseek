import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R10

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok10_0 : closOK cmT labT10 stabT10 grepT10 [0,1,2,3,4] (List.range 399) = true := by decide +kernel
theorem clos_ok10_1 : closOK cmT labT10 stabT10 grepT10 [5,6,7,8,9] (List.range 399) = true := by decide +kernel
theorem clos_ok10_2 : closOK cmT labT10 stabT10 grepT10 [10,11,12,13,14] (List.range 399) = true := by decide +kernel
theorem clos_ok10_3 : closOK cmT labT10 stabT10 grepT10 [15,16,17,18,19] (List.range 399) = true := by decide +kernel
theorem clos_ok10_4 : closOK cmT labT10 stabT10 grepT10 [20,21,22,23,24] (List.range 399) = true := by decide +kernel
theorem clos_ok10_5 : closOK cmT labT10 stabT10 grepT10 [25,26,27,28,29] (List.range 399) = true := by decide +kernel
theorem clos_ok10_6 : closOK cmT labT10 stabT10 grepT10 [30,31,32,33,34] (List.range 399) = true := by decide +kernel
theorem clos_ok10_7 : closOK cmT labT10 stabT10 grepT10 [35,36,37,38,39] (List.range 399) = true := by decide +kernel
theorem clos_ok10_8 : closOK cmT labT10 stabT10 grepT10 [40,41,42,43,44] (List.range 399) = true := by decide +kernel
theorem clos_ok10_9 : closOK cmT labT10 stabT10 grepT10 [45,46,47] (List.range 399) = true := by decide +kernel

end Submission.PTCert.C
end
