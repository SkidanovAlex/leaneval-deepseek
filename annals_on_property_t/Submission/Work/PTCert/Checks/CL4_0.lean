import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem clos_ok4_0 : closOK cmT labT4 stabT4 grepT4 [0,1,2,3,4,5,6,7] (List.range 248) = true := by decide +kernel
theorem clos_ok4_1 : closOK cmT labT4 stabT4 grepT4 [8,9,10,11,12,13,14,15] (List.range 248) = true := by decide +kernel
theorem clos_ok4_2 : closOK cmT labT4 stabT4 grepT4 [16,17,18,19,20,21,22,23] (List.range 248) = true := by decide +kernel
theorem clos_ok4_3 : closOK cmT labT4 stabT4 grepT4 [24,25,26,27,28,29,30,31] (List.range 248) = true := by decide +kernel
theorem clos_ok4_4 : closOK cmT labT4 stabT4 grepT4 [32,33,34,35,36,37,38,39] (List.range 248) = true := by decide +kernel
theorem clos_ok4_5 : closOK cmT labT4 stabT4 grepT4 [40,41,42,43,44,45,46,47] (List.range 248) = true := by decide +kernel
theorem clos_ok4_6 : closOK cmT labT4 stabT4 grepT4 [48,49,50,51,52,53,54,55] (List.range 248) = true := by decide +kernel
theorem clos_ok4_7 : closOK cmT labT4 stabT4 grepT4 [56,57,58,59,60,61,62,63] (List.range 248) = true := by decide +kernel
theorem clos_ok4_8 : closOK cmT labT4 stabT4 grepT4 [64,65,66,67,68,69,70,71] (List.range 248) = true := by decide +kernel
theorem clos_ok4_9 : closOK cmT labT4 stabT4 grepT4 [72,73,74,75,76,77,78,79] (List.range 248) = true := by decide +kernel
theorem clos_ok4_10 : closOK cmT labT4 stabT4 grepT4 [80,81,82,83,84,85,86,87] (List.range 248) = true := by decide +kernel
theorem clos_ok4_11 : closOK cmT labT4 stabT4 grepT4 [88,89,90,91,92,93,94,95] (List.range 248) = true := by decide +kernel

end Submission.PTCert.C
end
