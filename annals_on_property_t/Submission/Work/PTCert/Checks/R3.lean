import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok3 : eqL (scanRow cmT rowIdxT 1 3 131 pcL) stabL3 = true := by decide +kernel
theorem stabtab_ok3 : tabsOK stabL3 stabT3 = true := by decide +kernel
theorem sizes_ok3 : Nat.beq (sumL sizes3) 4641 && Nat.beq sizes3.length (ngL.getD 3 0) = true := by decide +kernel
theorem grep_ok3 : grepOK eM labT3 grepT3 215 = true := by decide +kernel
theorem gsz_ok3 : eqL sizes3 (gsz3_0 ++ gsz3_1 ++ gsz3_2 ++ gsz3_3 ++ gsz3_4 ++ gsz3_5 ++ gsz3_6) = true := by decide +kernel
theorem mem_ok3_0 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_0 gsz3_0 0 = true := by decide +kernel
theorem mem_ok3_1 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_1 gsz3_1 52 = true := by decide +kernel
theorem mem_ok3_2 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_2 gsz3_2 103 = true := by decide +kernel
theorem mem_ok3_3 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_3 gsz3_3 126 = true := by decide +kernel
theorem mem_ok3_4 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_4 gsz3_4 158 = true := by decide +kernel
theorem mem_ok3_5 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_5 gsz3_5 186 = true := by decide +kernel
theorem mem_ok3_6 : memGroupsOK cmT eM labT3 stabT3 grepT3 gl3_6 gsz3_6 204 = true := by decide +kernel

end Submission.PTCert.C
end
