import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.MeanSqPiece.meanSq3dE3
import Submission.Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean
import Submission.Work.SmallBoxTBWord.isCompact_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.MeanSqPiece.meanSqReal` — the real-valued sliding-box
mean-square bound

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

`Work.BoseFixB1B.MeanSqPiece.E3.meanSq3d_E3_holds` proves, for a measurable
`W : E3 → ℝ≥0∞` and `0 < d ≤ 1`,

    `∫⁻ u, ((∫⁻_{x ∈ B(u)} W x)/|B(u)|)² ≤ ofReal((9/(ℓd))³)·∫⁻_{x ∈ acube ℓ} (W x)²`.

This file transcribes it to a **continuous real** function `w : E3 → ℝ`:

    `Integrable (u ↦ (⍍_{B(u)} w)²) ∧ ∫_u (⍍_{B(u)} w)² ≤ (9/(ℓd))³ ∫_{acube ℓ} w²`,

which is the form consumed by `Work.BoseFixB1B.meanSq_of_realE3` (hence by
`Work.BoseFixB1S.MeanSq`, the last open piece of the intersection-mean correction
`CorrInput`).  The transcription is the pointwise comparison

    `ofReal ((⍍_{B(u)}w)²) ≤ ((∫⁻_{x∈B(u)} ofReal|w x|)/|B(u)|)²`

(using `|∫_{B(u)}w| ≤ ∫_{B(u)}|w|`, `ofReal (boxMass) = |B(u)|`,
`ofReal (x⁻¹) ≤ (ofReal x)⁻¹`, `ofReal (B⁻¹·∫|w|) = ofReal(B⁻¹)·∫⁻ ofReal|w|` and
`ofReal (a²) = (ofReal |a|)²`), together with `integral_eq_lintegral_of_nonneg_ae`,
`hasFiniteIntegral_iff_ofReal` (for the integrability conjunct) and `ENNReal.toReal_mono`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.MeanSqPiece.Real

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Two elementary `ENNReal.ofReal` facts -/

/-- `ofReal (x⁻¹) ≤ (ofReal x)⁻¹` for `x ≥ 0` (equality for `x > 0`; both sides are `0`
at `x = 0`). -/
lemma ofReal_inv_le_inv {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, inv_zero, ENNReal.ofReal_zero, ENNReal.inv_zero]
    exact le_top
  · rw [ENNReal.ofReal_inv_of_pos h]

/-- `ofReal (a²) = (ofReal |a|)²`. -/
lemma ofReal_sq (a : ℝ) : ENNReal.ofReal (a ^ 2) = (ENNReal.ofReal |a|) ^ 2 := by
  have h1 : a ^ 2 = |a| * |a| := by rw [← sq_abs]; ring
  rw [h1, ENNReal.ofReal_mul (abs_nonneg a), sq]

/-! ## 2. `ofReal` of a set integral equals the set `lintegral` -/

/-- `ofReal (∫_{x ∈ s} |w x|) = ∫⁻_{x ∈ s} ofReal |w x|` for continuous `w` on a compact box. -/
lemma ofReal_setIntegral_abs_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    {w : E3 → ℝ} (hw : Continuous w) :
    ENNReal.ofReal (∫ x in Submission.BoseGases.dlBox ℓ d u, |w x|)
      = ∫⁻ x in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |w x| :=
  MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    ((hw.continuousOn.integrableOn_compact (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)).abs)
    (Filter.Eventually.of_forall fun x => abs_nonneg (w x))

/-- `ofReal (∫_{x ∈ acube ℓ} (w x)²) = ∫⁻_{x ∈ acube ℓ} ofReal ((w x)²)` for continuous `w`. -/
lemma ofReal_setIntegral_sq_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {w : E3 → ℝ} (hw : Continuous w) :
    ENNReal.ofReal (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2)
      = ∫⁻ x in Submission.BoseGases.acube ℓ, ENNReal.ofReal ((w x) ^ 2) :=
  MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    ((hw.pow 2).continuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ))
    (Filter.Eventually.of_forall fun x => sq_nonneg _)

/-! ## 3. The main transcription -/

theorem corrMeanSqReal_of_E3 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {w : E3 → ℝ} (hw : Continuous w) :
    MeasureTheory.Integrable (fun u : E3 =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
      ∧ (∫ u : E3,
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
        ≤ (9 / (ℓ * d)) ^ 3 *
          (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) := by
  set W : E3 → ℝ≥0∞ := fun x => ENNReal.ofReal |w x| with hWdef
  have hWm : Measurable W := hw.abs.measurable.ennreal_ofReal
  -- the box volume is the `ofReal` of the box mass
  have hvol : ∀ u : E3, volume (Submission.BoseGases.dlBox ℓ d u)
      = ENNReal.ofReal (Work.SmallBoxSliding.boxMass ℓ d u) := fun u => by
    rw [Work.SmallBoxSliding.ofReal_boxMass_eq hℓ u,
      Work.SmallBoxSliding.lintegral_ofReal_boxInd ℓ d u]
  -- the pointwise comparison
  have hpt : ∀ u : E3, ENNReal.ofReal
        (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
      ≤ ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / volume (Submission.BoseGases.dlBox ℓ d u)) ^ 2 := by
    intro u
    have hbm0 : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
      exact ENNReal.toReal_nonneg
    have hkey : ENNReal.ofReal
        |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x|
        ≤ (∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / volume (Submission.BoseGases.dlBox ℓ d u) := by
      have h1 : |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x|
          ≤ (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, |w x| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (MeasureTheory.norm_integral_le_integral_norm
            (fun x : E3 => w x)) (by positivity)
      calc ENNReal.ofReal |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ x in Submission.BoseGases.dlBox ℓ d u, w x|
          ≤ ENNReal.ofReal ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ x in Submission.BoseGases.dlBox ℓ d u, |w x|) :=
            ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹)
              * (∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x) := by
            rw [one_div, ENNReal.ofReal_mul (inv_nonneg.mpr hbm0),
              ofReal_setIntegral_abs_eq hℓ hd u hw, hWdef]
        _ ≤ (volume (Submission.BoseGases.dlBox ℓ d u))⁻¹
              * (∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0 : ℝ≥0∞) ≤ _)
            rw [hvol u]
            exact ofReal_inv_le_inv hbm0
        _ = (∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
              / volume (Submission.BoseGases.dlBox ℓ d u) := by
            rw [div_eq_mul_inv, mul_comm]
    calc ENNReal.ofReal
          (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
        = (ENNReal.ofReal |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x|) ^ 2 := ofReal_sq _
      _ ≤ ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
            / volume (Submission.BoseGases.dlBox ℓ d u)) ^ 2 :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ≥0∞) ≤ _) hkey 2
  -- integrate the pointwise comparison
  have hmono : (∫⁻ u : E3, ENNReal.ofReal
        (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2))
      ≤ ∫⁻ u : E3, ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / volume (Submission.BoseGases.dlBox ℓ d u)) ^ 2 :=
    lintegral_mono hpt
  have hE3 := Work.BoseFixB1B.MeanSqPiece.E3.meanSq3d_E3_holds hℓ hd hd1 hWm
  have hcube : (∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2)
      = ENNReal.ofReal (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) := by
    have h1 : (∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2)
        = ∫⁻ x in Submission.BoseGases.acube ℓ, ENNReal.ofReal ((w x) ^ 2) := by
      refine lintegral_congr fun x => ?_
      rw [hWdef]
      exact (ofReal_sq (w x)).symm
    rw [h1, ofReal_setIntegral_sq_eq hℓ hw]
  have hK : (0 : ℝ) ≤ (9 / (ℓ * d)) ^ 3 *
      (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) :=
    mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  have hbound : (∫⁻ u : E3, ENNReal.ofReal
        (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2))
      ≤ ENNReal.ofReal ((9 / (ℓ * d)) ^ 3 *
          (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2)) := by
    calc (∫⁻ u : E3, ENNReal.ofReal
          (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2))
        ≤ ∫⁻ u : E3, ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
            / volume (Submission.BoseGases.dlBox ℓ d u)) ^ 2 := hmono
      _ ≤ ENNReal.ofReal ((9 / (ℓ * d)) ^ 3)
            * ∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2 := hE3
      _ = ENNReal.ofReal ((9 / (ℓ * d)) ^ 3)
            * ENNReal.ofReal (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) := by
          rw [hcube]
      _ = ENNReal.ofReal ((9 / (ℓ * d)) ^ 3 *
            (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
  -- measurability of the integrand
  have hmeas : Measurable (fun u : E3 =>
      ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2) := by
    have h := (Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean hℓ hd hw).1
    simpa only [one_div] using h.pow_const 2
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun u => sq_nonneg _)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => sq_nonneg _) hmeas.aestronglyMeasurable]
    calc (∫⁻ u : E3, ENNReal.ofReal
          (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)).toReal
        ≤ (ENNReal.ofReal ((9 / (ℓ * d)) ^ 3 *
            (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = (9 / (ℓ * d)) ^ 3 *
            (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) :=
          ENNReal.toReal_ofReal hK

end Work.BoseFixB1B.MeanSqPiece.Real
