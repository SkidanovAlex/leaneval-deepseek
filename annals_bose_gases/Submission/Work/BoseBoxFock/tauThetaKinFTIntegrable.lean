import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable
import Submission.Work.BoseBoxFock.tauGapDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the low-frequency cap against the kinetic density

The cap `tauTheta c r = (max 0 (c - r))²` is **bounded by `c²`** for `c > 0` and `r ≥ 0`, so it
can never spoil the integrability of `p ↦ ‖kinFT g p‖²`:

    Integrable (fun p => tauTheta c ‖p‖ * ‖kinFT g p‖²)

for every smooth compactly supported `g` (`SqrtKin.kinFT_sq_integrable`), by the pointwise
domination `tauTheta c ‖p‖ ≤ c²` and `Integrable.mono'` against the majorant
`p ↦ c²·‖kinFT g p‖²`.

This is the low-frequency (`Θ_c`) half of `Submission.Work.BoseBoxFock.row_of_deficit`; the other
weight `tauPsi` is the convexity defect of the smoothed profile.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

/-- The cap is bounded by `c²`: for `c > 0` and `r ≥ 0`, `(max 0 (c - r))² ≤ c²`. -/
lemma tauTheta_le_sq {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : tauTheta c r ≤ c ^ 2 := by
  have h1 : max 0 (c - r) ≤ c := max_le (le_of_lt hc) (by linarith)
  have h0 : 0 ≤ max 0 (c - r) := le_max_left _ _
  rw [tauTheta]
  nlinarith [h1, h0, hc]

/-- The cap is nonnegative. -/
lemma tauTheta_nonneg (c r : ℝ) : 0 ≤ tauTheta c r := by
  rw [tauTheta]; positivity

/-- The function `p ↦ tauTheta c ‖p‖` is continuous. -/
lemma continuous_tauTheta_norm (c : ℝ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) => tauTheta c ‖p‖) := by
  have hcont1 : Continuous
      (fun p : EuclideanSpace ℝ (Fin 3) => max 0 (c - ‖p‖)) :=
    (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)).max
      ((continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 3) => c).sub
        continuous_norm)
  show Continuous (fun p : EuclideanSpace ℝ (Fin 3) => max 0 (c - ‖p‖) ^ 2)
  exact hcont1.pow 2

/-- **Integrability of the cap weight against the kinetic density**: for `c > 0` and `g` smooth
compactly supported, `p ↦ (c - ‖p‖)₊²·‖kinFT g p‖²` is integrable. -/
theorem tauThetaKinFTIntegrable {c : ℝ} (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseBoxFock.tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hsq := SqrtKin.kinFT_sq_integrable hg hgc
  have hcont := continuous_tauTheta_norm (c := c)
  show MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
    max 0 (c - ‖p‖) ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
  refine (hsq.const_mul (c ^ 2)).mono'
    (hcont.aestronglyMeasurable.mul hsq.aestronglyMeasurable) ?_
  filter_upwards with p
  have hnn : 0 ≤ max 0 (c - ‖p‖) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hnn (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (tauTheta_le_sq hc (norm_nonneg p)) (sq_nonneg _)

end Work.BoseBoxFock
