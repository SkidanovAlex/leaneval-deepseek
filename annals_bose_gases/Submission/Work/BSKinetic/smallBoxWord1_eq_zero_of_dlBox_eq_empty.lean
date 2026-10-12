import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-particle small-box word vanishes on an empty sliding box

FS's sliding small box is `B(u) = acube ℓ ∩ ((ℓd)•u + acube(ℓd))`
(`Submission.BoseGases.dlBox ℓ d u`).  Whenever this box is empty the whole word
`𝒯_{B(u)}` collapses:

* FS's box projection `Q_{B(u)} = 1_{B(u)} − P_{B(u)}` (`Work.UBBInputs8.boxQInd`) carries the box
  indicator, so on the empty box it is the **zero** function (and likewise
  `Work.UBBInputs8.boxPInd = 0`), hence
* the excited count `n₊(B(u)) = Σᵢ‖Q_{B(u),i}Φ‖²` (`Work.UBBInputs8.cnPlusBoxInd`) vanishes, and
* the windowed `p`-amplitudes `tBamp χ p (Q_{B(u),i}Φ)` (`Work.SmallBoxTBWord.tBamp`) - which are
  linear in the state - vanish too, so the `p`-diagonal kinetic form
  (`Work.UBBInputs8.tBdiagFormInd`) and its spectral specialisation
  (`Work.UBBInputs8.tBwordKinInd`) vanish.

Consequently `𝒯_{B(u)}` (`Work.UBBInputs8.tBwordInd`, and its sliding instantiation
`Work.UBBInputs8.tBwordBInd` = `smallBoxWord1`) is `0` - for *every* value of the gap coefficient
and the cutoff, and with the box volume `boxMass ℓ d u` (which is `0` here) playing no role,
because the `1/volA` factor multiplies the integral of a function over the empty set.

This is the `N = 1` piece of the round-8 audit `Work.UBBInputs8.A.not_integrable_tBwordB_const`:
on the far set (`dlBox ℓ d u = ∅`) FS's projection degenerates, so the repaired word carries no
spurious kinetic.  (The corpus's *indicator-free* projection `Work.SmallBoxTBWord.boxQ` does
**not** have this property: `Work.UBBInputs8.A.boxQ_empty_aux` shows it acts as the identity
there.) -/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. FS's box projection on the empty box -/

/-- The box condensate projection `P_{A,i}` over the empty box is `0`: its defining integral is
the integral of an arbitrary function over `∅`, and its box indicator vanishes. -/
lemma boxPInd_empty_eq_zero (volA : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA (∅ : Set ℝ³) i Φ = 0 := by
  funext x
  simp [Work.UBBInputs8.boxPInd]

/-- FS's mean-free projection `Q_{A,i} = 1_A − P_{A,i}` over the empty box is `0` (both terms
vanish). -/
lemma boxQInd_empty_eq_zero (volA : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) :
    Work.UBBInputs8.boxQInd volA (∅ : Set ℝ³) i Φ = 0 := by
  funext x
  simp [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]

/-- The excited count `n₊(A) = Σᵢ‖Q_{A,i}Φ‖²` of the empty box vanishes. -/
lemma cnPlusBoxInd_empty_eq_zero (a volA : ℝ) {N : ℕ} (Ψ : X N → ℝ) :
    Work.UBBInputs8.cnPlusBoxInd a (∅ : Set ℝ³) volA Ψ = 0 := by
  simp [Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]

/-! ## 2. The `p`-diagonal kinetic form on the empty box -/

/-- The `p`-diagonal kinetic form of the empty box vanishes: the windowed amplitude is linear in
the state, and the state is `Q_{∅,i}Φ = 0`. -/
lemma tBdiagFormInd_empty_eq_zero (a volA : ℝ) (χ : ℝ³ → ℝ) (F : ℝ → ℝ) {N : ℕ}
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.tBdiagFormInd a (∅ : Set ℝ³) volA χ F Ψ = 0 := by
  simp [Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd,
    Work.SmallBoxTBWord.tBamp]

/-- The spectral half of the empty-box word vanishes (specialisation of
`tBdiagFormInd_empty_eq_zero` to the symbol `fsKinCoeff c`). -/
lemma tBwordKinInd_empty_eq_zero (a volA : ℝ) (χ : ℝ³ → ℝ) (c : ℝ) {N : ℕ} (Ψ : X N → ℝ) :
    Work.UBBInputs8.tBwordKinInd a (∅ : Set ℝ³) volA χ c Ψ = 0 := by
  simp [Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.boxQInd,
    Work.UBBInputs8.boxPInd, Work.SmallBoxTBWord.tBamp]

/-! ## 3. The word `𝒯_{B(u)}` on the empty box -/

/-- **`𝒯_B = 0` for `B = ∅`**: both the gap half (`tbGapCoeff s ε · n₊(∅) = 0`) and the kinetic
half (`Q_{∅}[√−Δ−c]₊²Q_{∅} = 0`) vanish. -/
lemma tBwordInd_empty_eq_zero (a volA : ℝ) (χ : ℝ³ → ℝ) (s ε c : ℝ) {N : ℕ} (Ψ : X N → ℝ) :
    Work.UBBInputs8.tBwordInd a (∅ : Set ℝ³) volA χ s ε c Ψ = 0 := by
  simp [Work.UBBInputs8.tBwordInd, Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd,
    Work.SmallBoxTBWord.tBamp]

/-! ## 4. The requested statement -/

/-- **The one-particle small-box word vanishes on an empty sliding box.**  Since
`smallBoxWord1 ℓ d ε c u φ` is `Work.UBBInputs8.tBwordBInd 1 ℓ d ε c u φ`
`= 𝒯_{B(u)}` at `B(u) = dlBox ℓ d u`, `χ = chiB ℓ d u`, `s = ℓd`, the empty box makes every
term vanish (`tBwordInd_empty_eq_zero`). -/
theorem smallBoxWord1_eq_zero_of_dlBox_eq_empty {ℓ d ε c : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (φ : Submission.BoseGases.X 1 → ℝ)
    (h : Submission.BoseGases.dlBox ℓ d u = ∅) :
    Work.BSKinetic.smallBoxWord1 ℓ d ε c u φ = 0 := by
  simp only [Work.BSKinetic.smallBoxWord1, Work.UBBInputs8.tBwordBInd]
  rw [h]
  exact tBwordInd_empty_eq_zero ℓ (Work.SmallBoxSliding.boxMass ℓ d u) (chiB ℓ d u) (ℓ * d)
    ε c φ

end Work.BSKinetic
