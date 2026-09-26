import Mathlib
import Submission.Work.PTCert.OrbitKeysDefs

namespace Work.PTCert.OrbitKeys

set_option maxRecDepth 10000

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-- For `r < 18`, `grepEI 0 r` is the `EI`-element with code `x0c r` (given that this is a code
of `B₂`).  Uses `GroupSem`: the groups of row `0` are the rows, so `grepE 0 r = x0c r`. -/
lemma grepEI_zero_eq (hG : Submission.PTCert.G.GroupSem) {r : ℕ} (hr : r < 18)
    (hmem : Submission.PTCert.G.x0c r ∈ Submission.PTCert.G.eS) :
    grepEI 0 r = ⟨Submission.PTCert.G.x0c r, hmem⟩ := by
  apply Subtype.ext
  show (toEI (Submission.PTCert.G.grepE 0 r) Submission.PTCert.G.pt0).1 = Submission.PTCert.G.x0c r
  rw [hG.2.1 r hr]
  exact toEI_val Submission.PTCert.G.pt0 hmem

/-- Row `0` of `EI`: every element is `Sg`-conjugate to the row representative of its label. -/
theorem orbitConjZero (hA : Submission.PTCert.G.ActSetup) (hG : Submission.PTCert.G.GroupSem) (hRF : Submission.PTCert.G.RowFacts) (y : Submission.PTCert.G.EI) : ∃ σ ∈ Submission.PTCert.G.Sg, Submission.PTCert.G.fE y = σ * Submission.PTCert.G.fE (Work.PTCert.OrbitKeys.grepEI 0 (Submission.PTCert.G.labE 0 y.1)) * σ⁻¹ := by
  obtain ⟨_, _, hthird⟩ := hRF (fun _ => 0)
  obtain ⟨hr18, σ, hσ, x', hx'1, hx'act⟩ := hthird y
  obtain ⟨_, hconjact⟩ := hA.2.2.1
  have hconj := hconjact σ hσ x'
  have hmem : Submission.PTCert.G.x0c (Submission.PTCert.G.labE 0 y.1) ∈ Submission.PTCert.G.eS := by
    rw [← hx'1]; exact x'.2
  have hgrep : grepEI 0 (Submission.PTCert.G.labE 0 y.1) = x' := by
    rw [grepEI_zero_eq hG hr18 hmem]
    exact Subtype.ext hx'1.symm
  refine ⟨σ, hσ, ?_⟩
  calc Submission.PTCert.G.fE y
      = Submission.PTCert.G.fE (Submission.PTCert.G.actE σ x') := by rw [hx'act]
    _ = σ * Submission.PTCert.G.fE x' * σ⁻¹ := hconj
    _ = σ * Submission.PTCert.G.fE (grepEI 0 (Submission.PTCert.G.labE 0 y.1)) * σ⁻¹ := by rw [hgrep]

end Work.PTCert.OrbitKeys
