import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok4 : eqL (scanRow cmT rowIdxT 1 4 132 pcL) stabL4 = true := by decide +kernel
theorem stabtab_ok4 : tabsOK stabL4 stabT4 = true := by decide +kernel
theorem sizes_ok4 : Nat.beq (sumL sizes4) 4641 && Nat.beq sizes4.length (ngL.getD 4 0) = true := by decide +kernel
theorem grep_ok4 : grepOK eM labT4 grepT4 248 = true := by decide +kernel
theorem gsz_ok4 : eqL sizes4 (gsz4_0 ++ gsz4_1 ++ gsz4_2 ++ gsz4_3 ++ gsz4_4 ++ gsz4_5 ++ gsz4_6) = true := by decide +kernel
theorem mem_ok4_0 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_0 gsz4_0 0 = true := by decide +kernel
theorem mem_ok4_1 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_1 gsz4_1 59 = true := by decide +kernel
theorem mem_ok4_2 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_2 gsz4_2 120 = true := by decide +kernel
theorem mem_ok4_3 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_3 gsz4_3 148 = true := by decide +kernel
theorem mem_ok4_4 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_4 gsz4_4 183 = true := by decide +kernel
theorem mem_ok4_5 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_5 gsz4_5 216 = true := by decide +kernel
theorem mem_ok4_6 : memGroupsOK cmT eM labT4 stabT4 grepT4 gl4_6 gsz4_6 237 = true := by decide +kernel

end Submission.PTCert.C
end
