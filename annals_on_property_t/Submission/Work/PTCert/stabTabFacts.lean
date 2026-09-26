import Mathlib
import Submission.Work.PTCert.rowHelp
import Submission.Work.PTCert.tabSem

/-!
# `PTCert` — the letter-table facts for the stabiliser codes

For every `1 ≤ r < 18` the check `C.stabtab_ok r` (`Checks/R r.lean`) says `tabsOK stabLr stabTr = true`,
and `stabL r = stabLr`, `stabTab r i = (stabTr).get i` hold definitionally because
`stabL r = stabLs.getD r []` and `stabTab r i = (stabTs.getD r (NT.leaf 0)).get i` with `stabLs`/`stabTs`
the literal lists of the `17` per-row data.  Reading each check through `tabsOK_ith` and `tabOK_iff`
therefore gives, for every index `i` of the stabiliser list `stabL r`, that the code `(stabL r).getD i 0`
is a valid permutation code and that the table `stabTab r i` is its letter action — which is exactly the
last conjunct of `RowSem`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-- The `17` stabiliser letter-table checks of `Checks/R1..17.lean`, restated for `stabL`/`stabTs`:
for `1 ≤ r < 18` the table `stabTs.getD r (NT.leaf 0) = stabTr` is a correct letter table for the
stabiliser code list `stabL r = stabLr`. -/
theorem stabTab_checks (r : ℕ) (hr18 : r < 18) (hr1 : 1 ≤ r) :
    tabsOK (stabL r) (stabTs.getD r (NT.leaf 0)) = true := by
  interval_cases r
  · exact Submission.PTCert.C.stabtab_ok1
  · exact Submission.PTCert.C.stabtab_ok2
  · exact Submission.PTCert.C.stabtab_ok3
  · exact Submission.PTCert.C.stabtab_ok4
  · exact Submission.PTCert.C.stabtab_ok5
  · exact Submission.PTCert.C.stabtab_ok6
  · exact Submission.PTCert.C.stabtab_ok7
  · exact Submission.PTCert.C.stabtab_ok8
  · exact Submission.PTCert.C.stabtab_ok9
  · exact Submission.PTCert.C.stabtab_ok10
  · exact Submission.PTCert.C.stabtab_ok11
  · exact Submission.PTCert.C.stabtab_ok12
  · exact Submission.PTCert.C.stabtab_ok13
  · exact Submission.PTCert.C.stabtab_ok14
  · exact Submission.PTCert.C.stabtab_ok15
  · exact Submission.PTCert.C.stabtab_ok16
  · exact Submission.PTCert.C.stabtab_ok17

/-- Reading off the letter-table facts for the stabiliser codes.  For `1 ≤ r < 18` and every index `i`
of `stabL r`, the code `(stabL r).getD i 0` is a valid permutation code of `B₂` and the table
`stabTab r i` computes its letter action `actL 5 pc sc` on all `81` normalised codes; the auxiliary
bound `sc < 32` (a conjunct of `tabOK`) is deliberately dropped. -/
theorem stabTabFacts : ∀ r < 18, 1 ≤ r → ∀ i < (stabL r).length,
    validPC 5 ((stabL r).getD i 0 / 32) = true ∧
    ∀ k < 81, lk (stabTab r i) k = actL 5 ((stabL r).getD i 0 / 32) ((stabL r).getD i 0 % 32) k := by
  intro r hr18 hr1 i hi
  have hchk : tabsOK (stabL r) (stabTs.getD r (NT.leaf 0)) = true := stabTab_checks r hr18 hr1
  have hith := tabsOK_ith (stabL r) (stabTs.getD r (NT.leaf 0)) i hi hchk
  obtain ⟨hvpc, -, hlk⟩ :=
    (tabOK_iff ((stabL r).getD i 0 / 32) ((stabL r).getD i 0 % 32)
      ((stabTs.getD r (NT.leaf 0)).get i)).mp hith
  exact ⟨hvpc, hlk⟩

end Work.PTCert
