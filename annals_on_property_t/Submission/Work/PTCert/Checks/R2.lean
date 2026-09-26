import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok2 : eqL (scanRow cmT rowIdxT 1 1 129 pcL) stabL2 = true := by decide +kernel
theorem stabtab_ok2 : tabsOK stabL2 stabT2 = true := by decide +kernel
theorem sizes_ok2 : Nat.beq (sumL sizes2) 4641 && Nat.beq sizes2.length (ngL.getD 2 0) = true := by decide +kernel
theorem grep_ok2 : grepOK eM labT2 grepT2 399 = true := by decide +kernel
theorem gsz_ok2 : eqL sizes2 (gsz2_0 ++ gsz2_1 ++ gsz2_2 ++ gsz2_3 ++ gsz2_4 ++ gsz2_5 ++ gsz2_6) = true := by decide +kernel
theorem mem_ok2_0 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_0 gsz2_0 0 = true := by decide +kernel
theorem mem_ok2_1 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_1 gsz2_1 88 = true := by decide +kernel
theorem mem_ok2_2 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_2 gsz2_2 182 = true := by decide +kernel
theorem mem_ok2_3 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_3 gsz2_3 228 = true := by decide +kernel
theorem mem_ok2_4 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_4 gsz2_4 291 = true := by decide +kernel
theorem mem_ok2_5 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_5 gsz2_5 349 = true := by decide +kernel
theorem mem_ok2_6 : memGroupsOK cmT eM labT2 stabT2 grepT2 gl2_6 gsz2_6 379 = true := by decide +kernel

end Submission.PTCert.C
end
