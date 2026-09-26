import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R13

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok13 : eqL (scanRow cmT rowIdxT 1 33 161 pcL) stabL13 = true := by decide +kernel
theorem stabtab_ok13 : tabsOK stabL13 stabT13 = true := by decide +kernel
theorem sizes_ok13 : Nat.beq (sumL sizes13) 4641 && Nat.beq sizes13.length (ngL.getD 13 0) = true := by decide +kernel
theorem grep_ok13 : grepOK eM labT13 grepT13 1332 = true := by decide +kernel
theorem gsz_ok13 : eqL sizes13 (gsz13_0 ++ gsz13_1 ++ gsz13_2 ++ gsz13_3 ++ gsz13_4 ++ gsz13_5 ++ gsz13_6) = true := by decide +kernel
theorem mem_ok13_0 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_0 gsz13_0 0 = true := by decide +kernel
theorem mem_ok13_1 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_1 gsz13_1 233 = true := by decide +kernel
theorem mem_ok13_2 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_2 gsz13_2 488 = true := by decide +kernel
theorem mem_ok13_3 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_3 gsz13_3 675 = true := by decide +kernel
theorem mem_ok13_4 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_4 gsz13_4 894 = true := by decide +kernel
theorem mem_ok13_5 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_5 gsz13_5 1102 = true := by decide +kernel
theorem mem_ok13_6 : memGroupsOK cmT eM labT13 stabT13 grepT13 gl13_6 gsz13_6 1228 = true := by decide +kernel

end Submission.PTCert.C
end
