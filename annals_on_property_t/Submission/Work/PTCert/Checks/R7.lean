import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R7

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok7 : eqL (scanRow cmT rowIdxT 1 17 145 pcL) stabL7 = true := by decide +kernel
theorem stabtab_ok7 : tabsOK stabL7 stabT7 = true := by decide +kernel
theorem sizes_ok7 : Nat.beq (sumL sizes7) 4641 && Nat.beq sizes7.length (ngL.getD 7 0) = true := by decide +kernel
theorem grep_ok7 : grepOK eM labT7 grepT7 399 = true := by decide +kernel
theorem gsz_ok7 : eqL sizes7 (gsz7_0 ++ gsz7_1 ++ gsz7_2 ++ gsz7_3 ++ gsz7_4 ++ gsz7_5 ++ gsz7_6) = true := by decide +kernel
theorem mem_ok7_0 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_0 gsz7_0 0 = true := by decide +kernel
theorem mem_ok7_1 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_1 gsz7_1 88 = true := by decide +kernel
theorem mem_ok7_2 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_2 gsz7_2 182 = true := by decide +kernel
theorem mem_ok7_3 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_3 gsz7_3 228 = true := by decide +kernel
theorem mem_ok7_4 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_4 gsz7_4 291 = true := by decide +kernel
theorem mem_ok7_5 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_5 gsz7_5 349 = true := by decide +kernel
theorem mem_ok7_6 : memGroupsOK cmT eM labT7 stabT7 grepT7 gl7_6 gsz7_6 379 = true := by decide +kernel

end Submission.PTCert.C
end
