import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R11

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok11 : eqL (scanRow cmT rowIdxT 1 21 149 pcL) stabL11 = true := by decide +kernel
theorem stabtab_ok11 : tabsOK stabL11 stabT11 = true := by decide +kernel
theorem sizes_ok11 : Nat.beq (sumL sizes11) 4641 && Nat.beq sizes11.length (ngL.getD 11 0) = true := by decide +kernel
theorem grep_ok11 : grepOK eM labT11 grepT11 1332 = true := by decide +kernel
theorem gsz_ok11 : eqL sizes11 (gsz11_0 ++ gsz11_1 ++ gsz11_2 ++ gsz11_3 ++ gsz11_4 ++ gsz11_5 ++ gsz11_6) = true := by decide +kernel
theorem mem_ok11_0 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_0 gsz11_0 0 = true := by decide +kernel
theorem mem_ok11_1 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_1 gsz11_1 233 = true := by decide +kernel
theorem mem_ok11_2 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_2 gsz11_2 488 = true := by decide +kernel
theorem mem_ok11_3 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_3 gsz11_3 675 = true := by decide +kernel
theorem mem_ok11_4 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_4 gsz11_4 894 = true := by decide +kernel
theorem mem_ok11_5 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_5 gsz11_5 1102 = true := by decide +kernel
theorem mem_ok11_6 : memGroupsOK cmT eM labT11 stabT11 grepT11 gl11_6 gsz11_6 1228 = true := by decide +kernel

end Submission.PTCert.C
end
