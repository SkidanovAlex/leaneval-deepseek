import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.R10

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem scan_ok10 : eqL (scanRow cmT rowIdxT 1 20 148 pcL) stabL10 = true := by decide +kernel
theorem stabtab_ok10 : tabsOK stabL10 stabT10 = true := by decide +kernel
theorem sizes_ok10 : Nat.beq (sumL sizes10) 4641 && Nat.beq sizes10.length (ngL.getD 10 0) = true := by decide +kernel
theorem grep_ok10 : grepOK eM labT10 grepT10 399 = true := by decide +kernel
theorem gsz_ok10 : eqL sizes10 (gsz10_0 ++ gsz10_1 ++ gsz10_2 ++ gsz10_3 ++ gsz10_4 ++ gsz10_5 ++ gsz10_6) = true := by decide +kernel
theorem mem_ok10_0 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_0 gsz10_0 0 = true := by decide +kernel
theorem mem_ok10_1 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_1 gsz10_1 88 = true := by decide +kernel
theorem mem_ok10_2 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_2 gsz10_2 182 = true := by decide +kernel
theorem mem_ok10_3 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_3 gsz10_3 228 = true := by decide +kernel
theorem mem_ok10_4 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_4 gsz10_4 291 = true := by decide +kernel
theorem mem_ok10_5 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_5 gsz10_5 349 = true := by decide +kernel
theorem mem_ok10_6 : memGroupsOK cmT eM labT10 stabT10 grepT10 gl10_6 gsz10_6 379 = true := by decide +kernel

end Submission.PTCert.C
end
