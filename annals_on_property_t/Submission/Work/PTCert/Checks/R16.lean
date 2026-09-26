import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R16

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok16 : eqL (scanRow cmT rowIdxT 1 38 166 pcL) stabL16 = true := by decide +kernel
theorem stabtab_ok16 : tabsOK stabL16 stabT16 = true := by decide +kernel
theorem sizes_ok16 : Nat.beq (sumL sizes16) 4641 && Nat.beq sizes16.length (ngL.getD 16 0) = true := by decide +kernel
theorem grep_ok16 : grepOK eM labT16 grepT16 682 = true := by decide +kernel
theorem gsz_ok16 : eqL sizes16 (gsz16_0 ++ gsz16_1 ++ gsz16_2 ++ gsz16_3 ++ gsz16_4 ++ gsz16_5 ++ gsz16_6) = true := by decide +kernel
theorem mem_ok16_0 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_0 gsz16_0 0 = true := by decide +kernel
theorem mem_ok16_1 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_1 gsz16_1 120 = true := by decide +kernel
theorem mem_ok16_2 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_2 gsz16_2 252 = true := by decide +kernel
theorem mem_ok16_3 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_3 gsz16_3 346 = true := by decide +kernel
theorem mem_ok16_4 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_4 gsz16_4 456 = true := by decide +kernel
theorem mem_ok16_5 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_5 gsz16_5 560 = true := by decide +kernel
theorem mem_ok16_6 : memGroupsOK cmT eM labT16 stabT16 grepT16 gl16_6 gsz16_6 627 = true := by decide +kernel

end Submission.PTCert.C
end
