import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the sharp kinetic density `p ↦ [‖p‖−c]₊²·‖kinFT g p‖²`

For `g : ℝ³ → ℂ` smooth with compact support and `c ≥ 0`, the *sharp kinetic density*
`p ↦ fsKinCoeff c ‖p‖ · ‖kinFT g p‖²` (with `fsKinCoeff c r = (max (r − c) 0)²` the FS symbol
`[r−c]₊²`, and `kinFT` the `p`-convention Fourier transform) is integrable on `ℝ³`.

The reason is a **pointwise domination**: for `0 ≤ c` and `r ≥ 0`,
`(max (r − c) 0)² ≤ r²` — the positive part `r − c` is `≤ r` and the square is monotone on the
nonnegative reals.  So the density is dominated by `‖p‖²·‖kinFT g p‖²`, which is integrable for
smooth compactly supported `g` (`Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable`).  The
remaining measurability input is `Integrable.aestronglyMeasurable` of `‖kinFT g p‖²`
(`Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable`) together with the continuity of the symbol
`p ↦ fsKinCoeff c ‖p‖`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.FRK

/-- **The pointwise domination of the sharp kinetic symbol**: for `0 ≤ c` and `0 ≤ r`,
`fsKinCoeff c r = (max (r − c) 0)² ≤ r²`. -/
theorem fsKinCoeff_le_sq {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ r ^ 2 := by
  simp only [Submission.BoseGases.fsKinCoeff]
  have h1 : max (r - c) 0 ≤ r := max_le (by linarith) hr
  exact pow_le_pow_left₀ (le_max_right _ _) h1 2

/-- **Integrability of the sharp kinetic density** `p ↦ [‖p‖−c]₊²·‖kinFT g p‖²` for smooth
compactly supported `g : ℝ³ → ℂ` and `c ≥ 0`. -/
theorem integrable_fsKinCoeff_mul_kinFT_sq {c : ℝ} (hc : 0 ≤ c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  -- the dominating `‖p‖²`-weighted density is integrable
  have hK2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable (g := g) hg hgc
  -- and `‖kinFT g p‖²` is a.e. strongly measurable (indeed integrable)
  have hK : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable (g := g) hg hgc
  -- the symbol `p ↦ fsKinCoeff c ‖p‖ = (max (‖p‖ − c) 0)²` is continuous
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖) :=
    ((continuous_norm.sub continuous_const).max continuous_const).pow 2
  refine hK2.mono' (hcont.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq hc (norm_nonneg p)) (sq_nonneg _)

end Work.BoseBoxFock.FRK
