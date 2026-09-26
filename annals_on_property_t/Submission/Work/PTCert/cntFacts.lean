import Mathlib
import Submission.Work.PTCert.rowHelp

namespace Work.PTCert

/-
Goal: the stored row counts are the sizes of the labelled classes of `eAll`.

The check `Submission.PTCert.C.cnt_ok : cntOK eM repInfoT eAll cntL = true` (`Checks/G6.lean`) is
  `allIdx cntL (fun r c => Nat.beq (countL eAll (fun z => Nat.beq (lab0 eM repInfoT z) r)) c) 0 = true`.
`Work.PTCert.allIdx_eq_true` (rowHelp) turns this into
`∀ r < cntL.length, countL eAll (fun z => Nat.beq (lab0 eM repInfoT z) r) = cntL.getD r 0`;
`cntL.length = 18` and `Work.PTCert.countL_eq_filter_length (l) (p) : countL l p = (l.filter p).length`
(rowHelp) finish it (`Nat.beq_eq`).
-/
open Submission.PTCert Submission.PTCert.D

/-- The length of the stored count table. -/
theorem cntL_length : cntL.length = 18 := by decide +kernel

/-- The `cntOK` check, read as a `Prop` through `allIdx_eq_true`. -/
theorem cnt_countL (r : ℕ) (hr : r < cntL.length) :
    countL eAll (fun z => Nat.beq (lab0 eM repInfoT z) r) = cntL.getD r 0 := by
  have h := (allIdx_eq_true cntL
    (fun r c => Nat.beq (countL eAll (fun z => Nat.beq (lab0 eM repInfoT z) r)) c) 0).mp
    C.cnt_ok r hr
  rw [Nat.beq_eq] at h
  simpa using h

theorem cntFacts : ∀ r < 18,
    (eAll.filter (fun z => Nat.beq (lab0 eM repInfoT z) r)).length = cntL.getD r 0 := by
  intro r hr
  rw [← countL_eq_filter_length]
  exact cnt_countL r (by rw [cntL_length]; exact hr)

end Work.PTCert
