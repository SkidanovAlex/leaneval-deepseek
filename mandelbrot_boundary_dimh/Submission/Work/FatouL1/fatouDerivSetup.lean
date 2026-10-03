import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.crux
import Submission.Work.FatouL1.fatouCoordExistsL1

/-!
# FATOU-L1: the setup for `fatouSecondDerivBound` (definitions only)

The Fatou coordinate used throughout is the canonical one produced by the (proved) FATOU area
contract `Work.FatouCH.fatouCH` (conjunct `FatouExists`).  We fix it once here so that the lemmas
below (and any delegated children) can refer to it without re-choosing.

Notation (throughout the file `Submission/Work/FatouL1/fatouSecondDerivBound.lean`):
* `v := F - id`, `g := v - 1 = F' - 1`, so `v = 1 + g`;
* `u := Φ' - 1`;
* `m := u (· + 1) - u` (the unit-shift defect of `u`).
-/

open MandelDim Set

namespace Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- The canonical Fatou coordinate for a near-translation on `Qreg b₁ b₂`, taken from the proved
contract `Work.FatouCH.fatouCH` (its `FatouExists` conjunct). -/
noncomputable def fatouCoord (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) : ℂ → ℂ :=
  Classical.choose (fatouCoordExistsL1 b₁ b₂ F hadm hF)

theorem fatouCoord_spec (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) :
    MandelDim.IsFatouCoordOn F (fatouCoord hadm hF) (MandelDim.Qreg b₁ b₂) :=
  Classical.choose_spec (fatouCoordExistsL1 b₁ b₂ F hadm hF)

/-- `u := Φ' - 1`, the first-order defect of the Fatou coordinate. -/
noncomputable def fatouU (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) : ℂ → ℂ :=
  fun z => deriv (fatouCoord hadm hF) z - 1

/-- `m := u (· + 1) - u`, the unit-shift defect of `u`. -/
noncomputable def fatouM (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) : ℂ → ℂ :=
  fun z => fatouU hadm hF (z + 1) - fatouU hadm hF z

end

end Work.FatouL1
