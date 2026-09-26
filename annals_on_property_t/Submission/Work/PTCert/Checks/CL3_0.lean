import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok3_0 : closOK cmT labT3 stabT3 grepT3 [0,1,2,3,4,5,6,7,8] (List.range 215) = true := by decide +kernel
theorem clos_ok3_1 : closOK cmT labT3 stabT3 grepT3 [9,10,11,12,13,14,15,16,17] (List.range 215) = true := by decide +kernel
theorem clos_ok3_2 : closOK cmT labT3 stabT3 grepT3 [18,19,20,21,22,23,24,25,26] (List.range 215) = true := by decide +kernel
theorem clos_ok3_3 : closOK cmT labT3 stabT3 grepT3 [27,28,29,30,31,32,33,34,35] (List.range 215) = true := by decide +kernel
theorem clos_ok3_4 : closOK cmT labT3 stabT3 grepT3 [36,37,38,39,40,41,42,43,44] (List.range 215) = true := by decide +kernel
theorem clos_ok3_5 : closOK cmT labT3 stabT3 grepT3 [45,46,47,48,49,50,51,52,53] (List.range 215) = true := by decide +kernel
theorem clos_ok3_6 : closOK cmT labT3 stabT3 grepT3 [54,55,56,57,58,59,60,61,62] (List.range 215) = true := by decide +kernel
theorem clos_ok3_7 : closOK cmT labT3 stabT3 grepT3 [63,64,65,66,67,68,69,70,71] (List.range 215) = true := by decide +kernel
theorem clos_ok3_8 : closOK cmT labT3 stabT3 grepT3 [72,73,74,75,76,77,78,79,80] (List.range 215) = true := by decide +kernel
theorem clos_ok3_9 : closOK cmT labT3 stabT3 grepT3 [81,82,83,84,85,86,87,88,89] (List.range 215) = true := by decide +kernel
theorem clos_ok3_10 : closOK cmT labT3 stabT3 grepT3 [90,91,92,93,94,95] (List.range 215) = true := by decide +kernel

end Submission.PTCert.C
end
