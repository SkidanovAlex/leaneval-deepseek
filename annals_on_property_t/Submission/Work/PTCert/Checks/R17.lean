import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R17

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok17 : eqL (scanRow cmT rowIdxT 1 41 169 pcL) stabL17 = true := by decide +kernel
theorem stabtab_ok17 : tabsOK stabL17 stabT17 = true := by decide +kernel
theorem sizes_ok17 : Nat.beq (sumL sizes17) 4641 && Nat.beq sizes17.length (ngL.getD 17 0) = true := by decide +kernel
theorem grep_ok17 : grepOK eM labT17 grepT17 1621 = true := by decide +kernel
theorem gsz_ok17 : eqL sizes17 (gsz17_0 ++ gsz17_1 ++ gsz17_2 ++ gsz17_3 ++ gsz17_4 ++ gsz17_5 ++ gsz17_6) = true := by decide +kernel
theorem mem_ok17_0 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_0 gsz17_0 0 = true := by decide +kernel
theorem mem_ok17_1 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_1 gsz17_1 256 = true := by decide +kernel
theorem mem_ok17_2 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_2 gsz17_2 510 = true := by decide +kernel
theorem mem_ok17_3 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_3 gsz17_3 757 = true := by decide +kernel
theorem mem_ok17_4 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_4 gsz17_4 1004 = true := by decide +kernel
theorem mem_ok17_5 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_5 gsz17_5 1253 = true := by decide +kernel
theorem mem_ok17_6 : memGroupsOK cmT eM labT17 stabT17 grepT17 gl17_6 gsz17_6 1454 = true := by decide +kernel

end Submission.PTCert.C
end
