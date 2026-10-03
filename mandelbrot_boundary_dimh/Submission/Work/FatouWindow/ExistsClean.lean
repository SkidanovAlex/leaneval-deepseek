import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.crux
import Submission.Work.FatouCH.fatouCH

/-!
# A clean existence proof for a Fatou coordinate (interface, not mathematics)

`Work.FatouL1.fatouCoord` is defined in `Submission/Work/FatouL1/fatouDerivSetup.lean` as
`Classical.choose (Work.FatouL1.fatouCoordExistsL1 b₁ b₂ F hadm hF)`, where the *proof*
`Work.FatouL1.fatouCoordExistsL1` currently lives in the placeholder module
`Submission/Work/FatouL1/cruxTemp.lean` and is *unfilled* (no proof body).  Every theorem in the `L¹` chain that
mentions the canonical coordinate (`fatouCoord`, `fatouU`, `fatouM`) therefore depends on
an extra placeholder axiom, so no module in the area can pass an axiom audit before that
placeholder is replaced.

This module provides the *same* interface with a genuine proof, taken from the (proved,
axiom-clean) fatou coordinate of the uniformization route `Work.FatouCH.fatouCH`.  It is the
source of the coordinate in the re-homed, taint-free copy of the chain
(`Submission/Work/FatouWindow/*`).
-/

open MandelDim

namespace Work.FatouWindow

noncomputable section

/-- **Existence of a Fatou coordinate** (qualitative: no derivative bound, no surjectivity modulo
`ℤ`), derived from the proved FATOU contract `Work.FatouCH.fatouCH`. -/
theorem fatouCoordExistsClean : Work.FatouL1.FatouCoordExistsL1 := by
  intro b₁ b₂ F hadm hF
  obtain ⟨Φ, hΦ, -⟩ := (Work.FatouCH.fatouCH).1 b₁ b₂ F hadm hF.1
  exact ⟨Φ, hΦ⟩

end

end Work.FatouWindow
