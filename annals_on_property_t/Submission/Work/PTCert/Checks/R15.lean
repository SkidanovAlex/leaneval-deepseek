import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R15

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok15 : eqL (scanRow cmT rowIdxT 1 37 165 pcL) stabL15 = true := by decide +kernel
theorem stabtab_ok15 : tabsOK stabL15 stabT15 = true := by decide +kernel
theorem sizes_ok15 : Nat.beq (sumL sizes15) 4641 && Nat.beq sizes15.length (ngL.getD 15 0) = true := by decide +kernel
theorem grep_ok15 : grepOK eM labT15 grepT15 712 = true := by decide +kernel
theorem gsz_ok15 : eqL sizes15 (gsz15_0 ++ gsz15_1 ++ gsz15_2 ++ gsz15_3 ++ gsz15_4 ++ gsz15_5 ++ gsz15_6) = true := by decide +kernel
theorem mem_ok15_0 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_0 gsz15_0 0 = true := by decide +kernel
theorem mem_ok15_1 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_1 gsz15_1 128 = true := by decide +kernel
theorem mem_ok15_2 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_2 gsz15_2 268 = true := by decide +kernel
theorem mem_ok15_3 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_3 gsz15_3 367 = true := by decide +kernel
theorem mem_ok15_4 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_4 gsz15_4 480 = true := by decide +kernel
theorem mem_ok15_5 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_5 gsz15_5 591 = true := by decide +kernel
theorem mem_ok15_6 : memGroupsOK cmT eM labT15 stabT15 grepT15 gl15_6 gsz15_6 657 = true := by decide +kernel

end Submission.PTCert.C
end
