import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R14

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok14 : eqL (scanRow cmT rowIdxT 1 34 162 pcL) stabL14 = true := by decide +kernel
theorem stabtab_ok14 : tabsOK stabL14 stabT14 = true := by decide +kernel
theorem sizes_ok14 : Nat.beq (sumL sizes14) 4641 && Nat.beq sizes14.length (ngL.getD 14 0) = true := by decide +kernel
theorem grep_ok14 : grepOK eM labT14 grepT14 1332 = true := by decide +kernel
theorem gsz_ok14 : eqL sizes14 (gsz14_0 ++ gsz14_1 ++ gsz14_2 ++ gsz14_3 ++ gsz14_4 ++ gsz14_5 ++ gsz14_6) = true := by decide +kernel
theorem mem_ok14_0 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_0 gsz14_0 0 = true := by decide +kernel
theorem mem_ok14_1 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_1 gsz14_1 233 = true := by decide +kernel
theorem mem_ok14_2 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_2 gsz14_2 488 = true := by decide +kernel
theorem mem_ok14_3 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_3 gsz14_3 675 = true := by decide +kernel
theorem mem_ok14_4 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_4 gsz14_4 894 = true := by decide +kernel
theorem mem_ok14_5 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_5 gsz14_5 1102 = true := by decide +kernel
theorem mem_ok14_6 : memGroupsOK cmT eM labT14 stabT14 grepT14 gl14_6 gsz14_6 1228 = true := by decide +kernel

end Submission.PTCert.C
end
