import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixB1B.matchedSlidingBCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.cubeWordDefs` — the matched (cube-cutoff) sliding word, named

Holder of `Submission/Work/BoseFixB1B/kineticHalfCube_of_oneBody.lean`.  The matched kinetic word
`Work.BoseFixB1B.sbKinCube` of `matchedWindowDefs.lean` is, definitionally, the FS-faithful
localised word `Work.UBBInputs8.tBwordInd` at the sliding box `B(u) = dlBox ℓ d u`, the box volume
`|B(u)| = boxMass ℓ d u`, the **cube** window `chiSmallB M ℓ d u` and the sliding cut-off
`c = sbCut μ (a v)`:

    cubeWord M ℓ d ε c u Φ  =  𝒯_{B(u)}  =  tbGapCoeff (ℓd) ε · n₊(B(u)) + Q_B χ_B[√−Δ−c]₊² χ_B Q_B .

This module *names* that word (so that the slot-decomposition lemmas about it can be stated), and
records the identification with `sbKinCube` at FS's parameters.  Definitions and one `rfl`-level
lemma only, hence `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The matched (cube-cutoff) localised sliding word** `𝒯_{B(u)}` at the box `B(u) = dlBox ℓ d u`,
the volume `|B(u)| = boxMass ℓ d u`, the cube window `chiSmallB M ℓ d u` and the spectral
cut-off `c`: this is `Work.UBBInputs8.tBwordInd` — the FS `eq:appTB` word with FS's own box
projection `Q_{B(u)} = 1_{B(u)} − P_{B(u)}`. -/
noncomputable def cubeWord (M : ℕ) (ℓ d ε c : ℝ) (u : E3) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
    (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) (ℓ * d) ε c Φ

/-- **The matched kinetic word is the cube-windowed localised word at FS's parameters.**  By
definition `sbKinCube = bGapCoeff v μ · n₊(B(u)) + bSpectralCube`, and `bGapCoeff v μ` is
`tbGapCoeff (bSide v μ * bD v μ) ε_T` while `cubeSpectral` is the `chiSmallB`-windowed spectral
slot, so this is `rfl`. -/
theorem sbKinCube_eq_cubeWord (v : E3 → ℝ) (μ : ℝ) (u : E3) {n : ℕ} (Φ : X n → ℝ) :
    sbKinCube v μ u Φ
      = cubeWord (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u Φ := rfl

/-- The `M`-slot of FS's parameters is the fixed regularity `Work.BoseBox.mValue` (it is
`48`, see `Work.BoseBox.mValue`; in particular it is `≥ 4`, which is what the `C³`-window
estimates need). -/
theorem bM_eq_mValue (v : E3 → ℝ) (μ : ℝ) : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := rfl

/-- `Work.BoseBox.mValue ≥ 4`. -/
theorem four_le_mValue : 4 ≤ Work.BoseBox.mValue := by
  rw [Work.BoseBox.mValue]; norm_num

end Work.BoseFixB1B
