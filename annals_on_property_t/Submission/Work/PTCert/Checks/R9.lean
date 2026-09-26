import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R9

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok9 : eqL (scanRow cmT rowIdxT 1 19 147 pcL) stabL9 = true := by decide +kernel
theorem stabtab_ok9 : tabsOK stabL9 stabT9 = true := by decide +kernel
theorem sizes_ok9 : Nat.beq (sumL sizes9) 4641 && Nat.beq sizes9.length (ngL.getD 9 0) = true := by decide +kernel
theorem grep_ok9 : grepOK eM labT9 grepT9 399 = true := by decide +kernel
theorem gsz_ok9 : eqL sizes9 (gsz9_0 ++ gsz9_1 ++ gsz9_2 ++ gsz9_3 ++ gsz9_4 ++ gsz9_5 ++ gsz9_6) = true := by decide +kernel
theorem mem_ok9_0 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_0 gsz9_0 0 = true := by decide +kernel
theorem mem_ok9_1 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_1 gsz9_1 88 = true := by decide +kernel
theorem mem_ok9_2 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_2 gsz9_2 182 = true := by decide +kernel
theorem mem_ok9_3 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_3 gsz9_3 228 = true := by decide +kernel
theorem mem_ok9_4 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_4 gsz9_4 291 = true := by decide +kernel
theorem mem_ok9_5 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_5 gsz9_5 349 = true := by decide +kernel
theorem mem_ok9_6 : memGroupsOK cmT eM labT9 stabT9 grepT9 gl9_6 gsz9_6 379 = true := by decide +kernel

end Submission.PTCert.C
end
