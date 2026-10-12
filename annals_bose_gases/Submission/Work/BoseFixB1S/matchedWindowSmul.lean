import ChallengeDeps
import Submission.Work.BoseFixB1B.fibreWord_smul
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1S.boxQSumScaleB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.matchedWindowSmul` — the matched-window words are quadratic forms

The matched (single cube cutoff) chapter's per-box ledgers (`countBoxCubeB1`'s middle arm,
`InBoxTotalCube`, `sbWordCube_ge_meanFieldRow`) are stated for **normalised** states
(`∫Φ² = 1`), because that is where the proved rung
`Work.BoseFixB1S.sbWordCube_ge_a0Main_add_boxA2` and the port apply, while the targets
(`Work.BoseFixB1B.CbbMiddleArm`, `Work.BoseFixB1S.InBoxTotalCube`) are un-normalised.  The
passage from the normalised to the general case is the **quadratic homogeneity** of both sides
of the inequalities, which was recorded as missing (in particular for `sbWordCube`, whose
scaling was not on disk: the frozen `sbWord` has `Work.BoseFixB1S.wordHomogeneityB1` /
`Work.BoseFixB1B.sectorIneqScale.sbKin_const_mul`, but the matched word does not).

Everything here is *mechanical*: `sbKinCube = bGapCoeff·cnPlusBoxInd + cubeSpectral` and
`cubeSpectral` is `tBdiagFormInd … χ (fsKinCoeff c) …`, so the two public scaling lemmas
`Work.BoseFixB1B.cnPlusBoxInd_const_mul` and `Work.BoseFixB1B.tBdiagFormInd_const_mul`
(`Work.hlocWire.tBdiagFormInd_smul`) apply term by term; `sbPot = qLHSwordB`
(`Work.BoseFixB1B.qLHSwordB_const_mul`), and the box counts `boxFlatCount`/`boxPairCount`/
`boxA2` scale through `Work.hlocWire.boxPInd_smul`/`boxQInd_smul` (`Work.BoseFixB1S.boxQSumScaleB1`
covers the whole `boxQSum`, hence `boxA2`).

`#print axioms` of all four is `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The matched-window kinetic word -/

/-- **The cube-windowed spectral slot is `2`-homogeneous in the state**:
`cubeSpectral v μ (t • Φ) u = t² · cubeSpectral v μ Φ u`.  It is `tBdiagFormInd` at the cube window
`chiSmallB` and the FS kinetic cut `fsKinCoeff (sbCut μ (a v))`. -/
theorem cubeSpectral_smul {v : E3 → ℝ} {μ : ℝ} {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) (t : ℝ) :
    Work.BoseFixB1B.cubeSpectral v μ (fun x => t * Φ x) u
      = t ^ 2 * Work.BoseFixB1B.cubeSpectral v μ Φ u := by
  unfold Work.BoseFixB1B.cubeSpectral Work.UBBInputs8.tBwordKinInd
  exact Work.BoseFixB1B.tBdiagFormInd_const_mul (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
    (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u)
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) Φ t

/-- **The matched kinetic word `sbKinCube` is `2`-homogeneous in the state.** -/
theorem sbKinCube_smul {v : E3 → ℝ} {μ : ℝ} {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) (t : ℝ) :
    Work.BoseFixB1B.sbKinCube v μ u (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1B.sbKinCube v μ u Φ := by
  unfold Work.BoseFixB1B.sbKinCube
  rw [Work.BoseFixB1B.cnPlusBoxInd_const_mul (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u) Φ t, cubeSpectral_smul u Φ t]
  ring

/-! ## 2. The potential word `sbPot = qLHSwordB`, and the matched sliding word -/

/-- **The small-box potential word `sbPot` is `2`-homogeneous in the state.** -/
theorem sbPot_smul {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ} {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) (t : ℝ) :
    Work.BoseFixB1.sbPot h μ u (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1.sbPot h μ u Φ := by
  unfold Work.BoseFixB1.sbPot
  exact Work.BoseFixB1B.qLHSwordB_const_mul h _ _ _ _ u Φ t

/-- **The matched sliding word `sbWordCube = sbKinCube + sbPot` is `2`-homogeneous in the state** —
the homogeneity needed to pass the matched per-box ledgers (all stated for `∫Φ² = 1`) to the
un-normalised targets. -/
theorem sbWordCube_smul {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ} {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) (t : ℝ) :
    Work.BoseFixB1B.sbWordCube v h μ u (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1B.sbWordCube v h μ u Φ := by
  unfold Work.BoseFixB1B.sbWordCube
  rw [sbKinCube_smul u Φ t, sbPot_smul h u Φ t]
  ring

/-- **`∫ (t·Φ)² = t²∫Φ²`** over the analysis box — the trivial half of the homogeneity of the
state norm that both sides of the per-box ledger carry. -/
theorem normB_smul' {ℓ : ℝ} {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (t : ℝ) :
    (∫ x in Submission.BoseGases.abox n ℓ, (t * Φ x) ^ 2)
      = t ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end Work.BoseFixB1S
