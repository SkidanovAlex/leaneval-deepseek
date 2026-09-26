import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R8

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok8 : eqL (scanRow cmT rowIdxT 1 18 146 pcL) stabL8 = true := by decide +kernel
theorem stabtab_ok8 : tabsOK stabL8 stabT8 = true := by decide +kernel
theorem sizes_ok8 : Nat.beq (sumL sizes8) 4641 && Nat.beq sizes8.length (ngL.getD 8 0) = true := by decide +kernel
theorem grep_ok8 : grepOK eM labT8 grepT8 399 = true := by decide +kernel
theorem gsz_ok8 : eqL sizes8 (gsz8_0 ++ gsz8_1 ++ gsz8_2 ++ gsz8_3 ++ gsz8_4 ++ gsz8_5 ++ gsz8_6) = true := by decide +kernel
theorem mem_ok8_0 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_0 gsz8_0 0 = true := by decide +kernel
theorem mem_ok8_1 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_1 gsz8_1 88 = true := by decide +kernel
theorem mem_ok8_2 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_2 gsz8_2 182 = true := by decide +kernel
theorem mem_ok8_3 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_3 gsz8_3 228 = true := by decide +kernel
theorem mem_ok8_4 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_4 gsz8_4 291 = true := by decide +kernel
theorem mem_ok8_5 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_5 gsz8_5 349 = true := by decide +kernel
theorem mem_ok8_6 : memGroupsOK cmT eM labT8 stabT8 grepT8 gl8_6 gsz8_6 379 = true := by decide +kernel

end Submission.PTCert.C
end
