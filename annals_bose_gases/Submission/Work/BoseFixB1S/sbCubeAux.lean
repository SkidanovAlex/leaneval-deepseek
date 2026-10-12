import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds
import Submission.Work.BoseFixB1S.CubeWindow.marginalCube
import Submission.Work.BoseFixB1S.CubeWindowKinetic
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.sbCubeAux` — auxiliary analytic bricks for
# `Work.BoseFixB1S.sbWordCubeIntegrable`

The target `Work.BoseFixB1S.sbWordCubeIntegrable` needs the `u`-marginal integrability of the
**matched (single cube cutoff) sliding word** `sbWordCube = sbKinCube + sbPot`, i.e. of
`Work.BoseFixB1B.bSpectralCube v μ Φ u = tBwordKinInd ℓ B(u) |B(u)| χ_{B(u)} c Φ` with the *cube*
window `chiSmallB` (which is only `C^{M-1}`, unlike the `C^∞` ball window `chiB` of the frozen
chapter).  This module collects the three analytic bricks that the frozen argument
(`Work.BoseFixB1.integrable_tBwordBInd`) does **not** provide at the cube cutoff:

* `chiSmallB_iteratedFDeriv_bound` — uniform-in-`u` bounds on the iterated derivatives
  (`k ≤ 3`) of the complexified cube window, together with its (uniform) support radius;
  the corpus's `C^∞` bound `Work.SmallBoxTBWord.chi_support_and_deriv_bound` cannot be used
  because `chiSmallB` is only `C^{M-1}`;
* `tBamp_decay3` — the `(1+‖p‖)⁻³` decay of the windowed amplitude `tBamp` at **`C³`**
  regularity (the `C^∞` version `Work.SmallBoxTBWord.tBamp_decay` does not apply);
* `aestronglyMeasurable_cnPlusBoxInd`, `aestronglyMeasurable_cubeSpectral` — the `u`-marginals
  are a.e. strongly measurable (parametric-integral device, needs only *continuity* of the
  window in `(u,z)` and of the state).

-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.BoseFixB1S.SbCubeAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 4. The cube window vanishes off the fixed centre cube -/

/-- A word with a zero window is zero. -/
lemma tBwordKinInd_eq_zero_of_window_zero {a volA c : ℝ} {A : Set E3} {N : ℕ} {χ : E3 → ℝ}
    (hχ : χ = fun _ => 0) (Φ : X N → ℝ) :
    Work.UBBInputs8.tBwordKinInd a A volA χ c Φ = 0 := by
  have hpw : ∀ (i : Fin N) (p : E3) (x : X N),
      Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x = 0 := by
    intro i p x
    rw [Work.SmallBoxTBWord.tBamp, hχ]
    simp
  simp only [Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = fun _ => 0 := by
    funext p
    have h1 : (fun x : X N => ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2) = fun _ => 0 := by
      funext x
      rw [hpw i p x]
      simp
    rw [h1, integral_zero]
    simp
  rw [h0]
  simp

/-- **The cube-windowed spectral word vanishes away from the centre cube
`acube ((1+d)/d)`**: off it the cube window `chiSmallB` is identically zero
(`Work.BoseFixB1S.CubeWindow.chiSmallB_eq_zero_of_not_mem_acube_u`). -/
lemma tBwordKinInd_cube_eq_zero_of_far {M : ℕ} (hM : 1 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {N : ℕ} (Φ : X N → ℝ) {u : E3}
    (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d)) :
    Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ = 0 := by
  have hχ : Submission.BoseGases.chiSmallB M ℓ d u = fun _ => 0 :=
    funext fun z =>
      Work.BoseFixB1S.CubeWindow.chiSmallB_eq_zero_of_not_mem_acube_u hM hℓ hd hu z
  rw [hχ]
  exact tBwordKinInd_eq_zero_of_window_zero (χ := fun _ => 0) (hχ := rfl) Φ

end Work.BoseFixB1S.SbCubeAux
