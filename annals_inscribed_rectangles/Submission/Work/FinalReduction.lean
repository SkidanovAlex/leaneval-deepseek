import Mathlib
import ChallengeDeps
import Submission.Work.AngleTransfer
import Submission.Commons.Measure.RealEndgame.ennreal_of_measureReal_ge

open InscribedRectangles
open Manifold Real MeasureTheory
open scoped ContDiff ENNReal

set_option autoImplicit false
noncomputable section

namespace Submission.FinalReduction

/-- `(1/3 : ℝ≥0∞) = ENNReal.ofReal (1/3)`. -/
lemma one_third_ennreal : (1 / 3 : ℝ≥0∞) = ENNReal.ofReal (1 / 3 : ℝ) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat 3]

/-- **Reduction of Theorem 1 to the measure data and the geometry.**

Let `γ` be a smooth Jordan curve and let `Good ⊆ ℝ/ℤ` be the (measurable, inversion-invariant)
set of angles `u = e^{iθ}` for which the Möbius strip of `γ` meets its rotation by `u`, of normalised
Haar measure at least `1/3`. If every `r ∈ [0,1]` whose half-angle point `e^{iπr}` lies in `Good`
gives rise to an inscribed rectangle of aspect ratio `tan (r·π/4)`, then `volume (X γ) ≥ 1/3`.

The measure-theoretic content of the proof is entirely contained here: the measure of `Good`, its
inversion invariance, and the geometric construction are the hypotheses. -/
theorem theorem_1_of_measure_data (γ : Circle → ℝ × ℝ) {Good : Set UnitAddCircle}
    (hmeas : MeasurableSet Good) (hneg : Good = -Good)
    (hμ : (1 / 3 : ℝ) ≤ volume.real Good)
    (hinc : {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ AngleTransfer.anglePoint (Real.pi * r) ∈ Good} ⊆ X γ) :
    volume (X γ) ≥ 1 / 3 := by
  have hthird := AngleTransfer.third_measure_of_neg_invariant hmeas hneg hμ
  have hfin : volume {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ AngleTransfer.anglePoint (Real.pi * r) ∈ Good}
      ≠ (⊤ : ℝ≥0∞) := by
    refine measure_ne_top_of_subset (s := Set.Icc 0 1) (t := _)
      (fun r hr => ⟨hr.1, hr.2.1⟩) ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have henn := Commons.Measure.RealEndgame.ennreal_of_measureReal_ge hfin hthird
  calc (1 / 3 : ℝ≥0∞) = ENNReal.ofReal (1 / 3 : ℝ) := one_third_ennreal
    _ ≤ volume {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ AngleTransfer.anglePoint (Real.pi * r) ∈ Good} := henn
    _ ≤ volume (X γ) := measure_mono hinc

end Submission.FinalReduction
