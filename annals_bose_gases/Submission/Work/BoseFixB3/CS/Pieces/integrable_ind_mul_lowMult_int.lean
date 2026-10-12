import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Reduce
import Submission.Work.BoseFixB3.HighMass.Base
import Submission.Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff
import Submission.Work.BoseFixB3.HighMassAux.lowMult_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.integrable_ind_mul_lowMult_int`

Integrability on the box of the low-momentum multiplier of an `L¹`-on-the-box function:

`x ↦ 1_{Λ}(x) · (f_L(√−Δ)G)(x) ∈ L¹(ℝ³)`

for `G ∈ L¹(Λ)` (no continuity of `G` is assumed — this is the "int" refinement of the
sibling `integrable_ind_mul_lowMult`, whose hypothesis is `Continuous G`).

## The argument

The momentum-space coefficient of the multiplier,

`c p = f(‖p‖/κ) · (θ_ΛG)^(p)`

(with `θ_ΛG` the extension by zero off the box), is integrable on momentum space
(`HighMassAux.integrable_lowMultCoeff`): the cut-off factor is compactly supported and the
Fourier transform of the `L¹` function `θ_ΛG` is bounded.  Writing the definition of
`lowMult` with the phase made explicit, the multiplier is the (real part of the) *inverse*
Fourier transform of `c`,

`lowMult fc κ ℓ G x = (2π)⁻³ · (kinFT c (−x)).re`,

so that `lowMult` is a continuous function of `x` (continuous Fourier transform of an `L¹`
function), and the standard integral estimate (`‖∫‖ ≤ ∫‖·‖`, `|Re z| ≤ ‖z‖`) bounds it
*uniformly*:

`|lowMult fc κ ℓ G x| ≤ (2π)⁻³ ∫_p ‖c p‖ =: B`  for every `x`.

Hence `1_Λ · lowMult` is a continuous (whence measurable) function times the indicator of a
set of finite measure `ℓ³`, and is dominated by `B · 1_Λ ∈ L¹(ℝ³)`, which gives
integrability.  (The bound is not `L¹` at large `x`: only the box restriction is used.)
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB3.CS.Pieces

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The momentum-space coefficient of the multiplier -/

/-- The momentum-space coefficient of the low-momentum multiplier applied to (the box
extension of) `G`:
`c p = f(‖p‖/κ) · kinFT (1_Λ · G) p`.  Its integrability is
`HighMassAux.integrable_lowMultCoeff` and drives everything below. -/
private noncomputable def lowCoeff (fc : LowCut) (κ ℓ : ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
    Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
      (((Submission.BoseGases.acube ℓ).indicator G z : ℝ) : ℂ)) p

/-- The cut-off `p ↦ f(‖p‖/κ)` (with `κ > 0`) is compactly supported: `f` vanishes on
`[2,∞)`, so the support lies in the closed ball of radius `2κ`. -/
private lemma hasCompactSupport_cutoff {fc : LowCut} {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) => fc.f (‖p‖ / κ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * κ))
    (isCompact_closedBall 0 (2 * κ)) ?_
  intro p hp
  simp only [Function.mem_support] at hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push_neg at h
  have h2 : 2 ≤ ‖p‖ / κ := by rw [le_div_iff₀ hκ]; linarith
  exact hp (fc.zero (‖p‖ / κ) h2)

/-! ## `lowMult` is the inverse Fourier transform of the coefficient -/

/-- **The defining identity of `lowMult` in terms of the coefficient `lowCoeff`**: the
`p`-integral of the definition is the `kinFT` of the coefficient at the momentum `−x`. -/
private lemma lowMult_eq_kinFT_lowCoeff (fc : LowCut) (κ ℓ : ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    lowMult fc κ ℓ G x
      = ((2 * Real.pi) ^ 3)⁻¹
          * (Submission.BoseGases.kinFT (lowCoeff fc κ ℓ G) (-x)).re := by
  unfold Work.BoseBoxFix.lowMult lowCoeff Submission.BoseGases.kinFT
  rw [Complex.re_ofReal_mul]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  have he : Complex.exp (Complex.I * (inner ℝ p x : ℂ))
      = Complex.exp (-(Complex.I * (inner ℝ (-x) p : ℂ))) := by
    rw [inner_neg_left, Complex.ofReal_neg, mul_neg, neg_neg, real_inner_comm]
  rw [he, mul_assoc]

/-- **Continuity of the multiplier in `x`**: `lowMult` is the real part of the (continuous)
Fourier transform of the `L¹` coefficient, composed with the reflection `x ↦ −x`. -/
private lemma continuous_lowMult (fc : LowCut) (κ ℓ : ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hc : MeasureTheory.Integrable (lowCoeff fc κ ℓ G)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 3) => lowMult fc κ ℓ G x) := by
  have hkin : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.kinFT (lowCoeff fc κ ℓ G) (-x)) :=
    (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hc).comp continuous_neg
  have hEq : (fun x : EuclideanSpace ℝ (Fin 3) => lowMult fc κ ℓ G x)
      = fun x : EuclideanSpace ℝ (Fin 3) =>
          ((2 * Real.pi) ^ 3)⁻¹
            * (Submission.BoseGases.kinFT (lowCoeff fc κ ℓ G) (-x)).re :=
    funext fun x => lowMult_eq_kinFT_lowCoeff fc κ ℓ G x
  rw [hEq]
  exact continuous_const.mul (Complex.continuous_re.comp hkin)

/-- **The uniform bound on the multiplier**: pointwise,
`|lowMult fc κ ℓ G x| ≤ (2π)⁻³ ∫_p ‖lowCoeff fc κ ℓ G p‖`, with a right-hand side
independent of `x`. -/
private lemma lowMult_abs_le (fc : LowCut) (κ ℓ : ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    |lowMult fc κ ℓ G x|
      ≤ ((2 * Real.pi) ^ 3)⁻¹
          * ∫ p : EuclideanSpace ℝ (Fin 3), ‖lowCoeff fc κ ℓ G p‖ := by
  rw [lowMult_eq_kinFT_lowCoeff]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |(Submission.BoseGases.kinFT (lowCoeff fc κ ℓ G) (-x)).re|
      ≤ ‖Submission.BoseGases.kinFT (lowCoeff fc κ ℓ G) (-x)‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ p : EuclideanSpace ℝ (Fin 3), ‖lowCoeff fc κ ℓ G p‖ := by
        calc ‖Submission.BoseGases.kinFT (lowCoeff fc κ ℓ G) (-x)‖
            = ‖∫ p : EuclideanSpace ℝ (Fin 3),
                Complex.exp (-(Complex.I * (inner ℝ (-x) p : ℂ)))
                  * lowCoeff fc κ ℓ G p‖ := rfl
          _ ≤ ∫ p : EuclideanSpace ℝ (Fin 3),
                ‖Complex.exp (-(Complex.I * (inner ℝ (-x) p : ℂ)))
                  * lowCoeff fc κ ℓ G p‖ := norm_integral_le_integral_norm _
          _ = ∫ p : EuclideanSpace ℝ (Fin 3), ‖lowCoeff fc κ ℓ G p‖ := by
              apply integral_congr_ae
              filter_upwards with p
              rw [norm_mul]
              simp [Complex.norm_exp]

/-! ## The target -/

theorem integrable_ind_mul_lowMult_int {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) {G : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : MeasureTheory.IntegrableOn G (Submission.BoseGases.acube ℓ)) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) x
        * Work.BoseBoxFix.lowMult fc κ ℓ G x) := by
  -- the momentum-space coefficient is `L¹`
  have hcs : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) => fc.f (‖p‖ / κ)) :=
    hasCompactSupport_cutoff (fc := fc) hκ
  have hc : MeasureTheory.Integrable (lowCoeff fc κ ℓ G) :=
    Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff hG hcs
  -- the uniform bound `B`
  set B : ℝ := ((2 * Real.pi) ^ 3)⁻¹
    * ∫ p : EuclideanSpace ℝ (Fin 3), ‖lowCoeff fc κ ℓ G p‖ with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (by positivity) (integral_nonneg fun p => norm_nonneg _)
  -- the dominating function `B · 1_Λ` is integrable
  have hΛ : MeasureTheory.Integrable
      ((Submission.BoseGases.acube ℓ).indicator
        (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))) := by
    refine (MeasureTheory.integrable_indicator_iff
      (Submission.BoseGases.acube_measurable ℓ)).mpr ?_
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_ne_top
    · simp
  have hdom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      B * (Submission.BoseGases.acube ℓ).indicator
        (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) x) :=
    hΛ.const_mul B
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · -- measurability: the box indicator times the continuous multiplier
    exact (Measurable.indicator measurable_const
      (Submission.BoseGases.acube_measurable ℓ)).aestronglyMeasurable.mul
      (continuous_lowMult fc κ ℓ G hc).aestronglyMeasurable
  · -- the pointwise domination
    filter_upwards with x
    by_cases hx : x ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hx, one_mul, mul_one, Real.norm_eq_abs]
      exact lowMult_abs_le fc κ ℓ G x
    · rw [Set.indicator_of_notMem hx]
      simp

end Work.BoseFixB3.CS.Pieces
