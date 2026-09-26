import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok6 : eqL (scanRow cmT rowIdxT 1 7 135 pcL) stabL6 = true := by decide +kernel
theorem stabtab_ok6 : tabsOK stabL6 stabT6 = true := by decide +kernel
theorem sizes_ok6 : Nat.beq (sumL sizes6) 4641 && Nat.beq sizes6.length (ngL.getD 6 0) = true := by decide +kernel
theorem grep_ok6 : grepOK eM labT6 grepT6 682 = true := by decide +kernel
theorem gsz_ok6 : eqL sizes6 (gsz6_0 ++ gsz6_1 ++ gsz6_2 ++ gsz6_3 ++ gsz6_4 ++ gsz6_5 ++ gsz6_6) = true := by decide +kernel
theorem mem_ok6_0 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_0 gsz6_0 0 = true := by decide +kernel
theorem mem_ok6_1 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_1 gsz6_1 120 = true := by decide +kernel
theorem mem_ok6_2 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_2 gsz6_2 253 = true := by decide +kernel
theorem mem_ok6_3 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_3 gsz6_3 346 = true := by decide +kernel
theorem mem_ok6_4 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_4 gsz6_4 456 = true := by decide +kernel
theorem mem_ok6_5 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_5 gsz6_5 560 = true := by decide +kernel
theorem mem_ok6_6 : memGroupsOK cmT eM labT6 stabT6 grepT6 gl6_6 gsz6_6 628 = true := by decide +kernel

end Submission.PTCert.C
end
