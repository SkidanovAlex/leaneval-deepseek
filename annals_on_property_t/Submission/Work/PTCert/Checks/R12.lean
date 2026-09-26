import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R12

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok12 : eqL (scanRow cmT rowIdxT 1 23 151 pcL) stabL12 = true := by decide +kernel
theorem stabtab_ok12 : tabsOK stabL12 stabT12 = true := by decide +kernel
theorem sizes_ok12 : Nat.beq (sumL sizes12) 4641 && Nat.beq sizes12.length (ngL.getD 12 0) = true := by decide +kernel
theorem grep_ok12 : grepOK eM labT12 grepT12 1332 = true := by decide +kernel
theorem gsz_ok12 : eqL sizes12 (gsz12_0 ++ gsz12_1 ++ gsz12_2 ++ gsz12_3 ++ gsz12_4 ++ gsz12_5 ++ gsz12_6) = true := by decide +kernel
theorem mem_ok12_0 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_0 gsz12_0 0 = true := by decide +kernel
theorem mem_ok12_1 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_1 gsz12_1 233 = true := by decide +kernel
theorem mem_ok12_2 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_2 gsz12_2 488 = true := by decide +kernel
theorem mem_ok12_3 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_3 gsz12_3 675 = true := by decide +kernel
theorem mem_ok12_4 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_4 gsz12_4 894 = true := by decide +kernel
theorem mem_ok12_5 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_5 gsz12_5 1102 = true := by decide +kernel
theorem mem_ok12_6 : memGroupsOK cmT eM labT12 stabT12 grepT12 gl12_6 gsz12_6 1228 = true := by decide +kernel

end Submission.PTCert.C
end
