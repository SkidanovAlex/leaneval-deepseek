import Mathlib
import Submission.Work.PTCert.CSAux
import Submission.Work.PTCert.cert1Aux
import Submission.Work.PTCert.rowHelp
import Submission.Work.PTCert.eChunkMem
import Submission.Work.PTCert.eExactFacts

set_option maxRecDepth 100000

noncomputable section

namespace Work.PTCert.CS

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-- The checker: every entry of the packed list `t` below `n` is a valid `B₂`-code
(namely `< 81 * 128`, with both its letter coordinates `< 81`). -/
def digOK (t : NT) (n : ℕ) : Bool :=
  allR n (fun g => decide (cG t g < 10368 ∧ cG t g % 128 < 81 ∧ cG t g / 128 < 81))

theorem digOK_spec {t : NT} {n : ℕ} (h : digOK t n = true) :
    ∀ g < n, cG t g < 10368 ∧ cG t g % 128 < 81 ∧ cG t g / 128 < 81 := by
  intro g hg
  have h' : decide (cG t g < 10368 ∧ cG t g % 128 < 81 ∧ cG t g / 128 < 81) = true :=
    (allR_iff_CSAux n _).mp h g hg
  exact of_decide_eq_true h'

theorem digOK_row (r : ℕ) (hr : r < 18) :
    digOK (grepTs.getD r (NT.leaf 0)) (ngE r) = true := by
  interval_cases r <;> (unfold digOK; decide +kernel)

theorem grepEDigits : ∀ r < 18, ∀ g < Submission.PTCert.G.ngE r,
    Submission.PTCert.G.grepE r g < 10368 ∧ Submission.PTCert.G.grepE r g % 128 < 81 ∧
      Submission.PTCert.G.grepE r g / 128 < 81 := by
  intro r hr g hg
  have h := digOK_spec (digOK_row r hr) g hg
  simpa only [grepE] using h

end Work.PTCert.CS
