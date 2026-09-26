import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R5

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok5 : eqL (scanRow cmT rowIdxT 1 5 133 pcL) stabL5 = true := by decide +kernel
theorem stabtab_ok5 : tabsOK stabL5 stabT5 = true := by decide +kernel
theorem sizes_ok5 : Nat.beq (sumL sizes5) 4641 && Nat.beq sizes5.length (ngL.getD 5 0) = true := by decide +kernel
theorem grep_ok5 : grepOK eM labT5 grepT5 1332 = true := by decide +kernel
theorem gsz_ok5 : eqL sizes5 (gsz5_0 ++ gsz5_1 ++ gsz5_2 ++ gsz5_3 ++ gsz5_4 ++ gsz5_5 ++ gsz5_6) = true := by decide +kernel
theorem mem_ok5_0 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_0 gsz5_0 0 = true := by decide +kernel
theorem mem_ok5_1 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_1 gsz5_1 233 = true := by decide +kernel
theorem mem_ok5_2 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_2 gsz5_2 488 = true := by decide +kernel
theorem mem_ok5_3 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_3 gsz5_3 675 = true := by decide +kernel
theorem mem_ok5_4 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_4 gsz5_4 894 = true := by decide +kernel
theorem mem_ok5_5 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_5 gsz5_5 1102 = true := by decide +kernel
theorem mem_ok5_6 : memGroupsOK cmT eM labT5 stabT5 grepT5 gl5_6 gsz5_6 1228 = true := by decide +kernel

end Submission.PTCert.C
end
