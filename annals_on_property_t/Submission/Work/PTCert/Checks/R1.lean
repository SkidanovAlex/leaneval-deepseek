import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok1 : eqL (scanRow cmT rowIdxT 0 1 1 pcL) stabL1 = true := by decide +kernel
theorem stabtab_ok1 : tabsOK stabL1 stabT1 = true := by decide +kernel
theorem sizes_ok1 : Nat.beq (sumL sizes1) 4641 && Nat.beq sizes1.length (ngL.getD 1 0) = true := by decide +kernel
theorem grep_ok1 : grepOK eM labT1 grepT1 399 = true := by decide +kernel
theorem gsz_ok1 : eqL sizes1 (gsz1_0 ++ gsz1_1 ++ gsz1_2 ++ gsz1_3 ++ gsz1_4 ++ gsz1_5 ++ gsz1_6) = true := by decide +kernel
theorem mem_ok1_0 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_0 gsz1_0 0 = true := by decide +kernel
theorem mem_ok1_1 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_1 gsz1_1 88 = true := by decide +kernel
theorem mem_ok1_2 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_2 gsz1_2 182 = true := by decide +kernel
theorem mem_ok1_3 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_3 gsz1_3 228 = true := by decide +kernel
theorem mem_ok1_4 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_4 gsz1_4 291 = true := by decide +kernel
theorem mem_ok1_5 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_5 gsz1_5 349 = true := by decide +kernel
theorem mem_ok1_6 : memGroupsOK cmT eM labT1 stabT1 grepT1 gl1_6 gsz1_6 379 = true := by decide +kernel

end Submission.PTCert.C
end
