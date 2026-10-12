import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Momentum.boxHat_eq_cubFT
import Submission.Work.BoseKinLoc.Momentum.cubFT_total
import Submission.Work.BoseKinLoc.Momentum.sm_cubFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integrable_momProj_Bh`

The sliding symbol of FS `eq:Q1Qslide`,

  `Bh ℓ q p = θ̂_ℓ(q − p) − ℓ⁻³ θ̂_ℓ p · θ̂_ℓ q`   (`θ̂_ℓ = boxHat ℓ`),

is **square-integrable** in `p` for `ℓ > 0`, with the `momProj`-cut-off inserted it is
`L¹`.  This is the decay (as opposed to the boundedness, used when a further `L²` weight
`‖fhat ψ‖²` is present) that the localisation estimates need: `boxHat ℓ` is the Fourier
transform of the indicator of the box `acube ℓ`, hence in `L²(ℝ³)` with the explicit
factorisation

  `boxHat ℓ p = ℓ³ · cubFT (ℓ • p)`,   `∫_ℝ³ (cubFT q)² dq < ∞` (`cubFT_total`),

so both terms of `Bh ℓ q ·` are in `L²`: the first is a translate of `boxHat ℓ`, the second
a constant multiple of it.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `boxHat ℓ` is square-integrable for `ℓ > 0`, by the scaling law
`boxHat ℓ p = ℓ³ cubFT (ℓ • p)` and the totality of `cubFT²` (`cubFT_total`). -/
private lemma integrable_boxHat_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable (fun p : ℝ³ => (Work.OneBodyKin.boxHat ℓ p) ^ 2) := by
  have h1 : MeasureTheory.Integrable (fun p : ℝ³ => (cubFT (ℓ • p)) ^ 2) :=
    (cubFT_total.1).comp_smul (ne_of_gt hℓ)
  refine (h1.const_mul ((ℓ ^ 3) ^ 2)).congr (Filter.Eventually.of_forall fun p => ?_)
  show (ℓ ^ 3) ^ 2 * (cubFT (ℓ • p)) ^ 2 = (Work.OneBodyKin.boxHat ℓ p) ^ 2
  rw [boxHat_eq_cubFT hℓ p]
  ring

/-- The translate of `boxHat ℓ²` by `q` is integrable (the profile is even). -/
private lemma integrable_boxHat_shift_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (q : ℝ³) :
    MeasureTheory.Integrable (fun p : ℝ³ => (Work.OneBodyKin.boxHat ℓ (q - p)) ^ 2) := by
  refine ((integrable_boxHat_sq hℓ).comp_sub_right q).congr
    (Filter.Eventually.of_forall fun p => ?_)
  show (Work.OneBodyKin.boxHat ℓ (p - q)) ^ 2 = (Work.OneBodyKin.boxHat ℓ (q - p)) ^ 2
  rw [show q - p = -(p - q) by abel, Work.OneBodyKin.boxHat_even]

/-- For `ℓ > 0` the box profile `q ↦ boxHat ℓ q` is continuous, by the scaling law
`boxHat ℓ q = ℓ³ cubFT (ℓ • q)` and continuity of `cubFT`. -/
private lemma continuous_boxHat_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun q : ℝ³ => Work.OneBodyKin.boxHat ℓ q) := by
  have hfun : (fun q : ℝ³ => Work.OneBodyKin.boxHat ℓ q)
      = fun q : ℝ³ => ℓ ^ 3 * cubFT (ℓ • q) :=
    funext fun q => boxHat_eq_cubFT hℓ q
  rw [hfun]
  exact continuous_const.mul (cubFT_continuous.comp (continuous_const_smul ℓ))

/-- `Bh ℓ q ·` is continuous in `p` for `ℓ > 0`. -/
private lemma continuous_Bh_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (q : ℝ³) :
    Continuous (fun p : ℝ³ => Bh ℓ q p) := by
  have hcont : Continuous (fun p : ℝ³ => Work.OneBodyKin.boxHat ℓ p) :=
    continuous_boxHat_of_pos hℓ
  have h1 : Continuous (fun p : ℝ³ => Work.OneBodyKin.boxHat ℓ (q - p)) :=
    hcont.comp (continuous_const.sub continuous_id)
  have h2 : Continuous
      (fun p : ℝ³ => (ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q) :=
    (continuous_const.mul hcont).mul continuous_const
  simp only [Bh]
  exact h1.sub h2

/-- **The sliding symbol is square-integrable.**  For `ℓ > 0` and fixed `q`,
`p ↦ (Bh ℓ q p)²` is integrable, since both of its two terms are translates/constants of
the `L²` profile `boxHat ℓ` (`integrable_boxHat_sq`). -/
private theorem integrable_Bh_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (q : ℝ³) :
    MeasureTheory.Integrable (fun p : ℝ³ => (Bh ℓ q p) ^ 2) := by
  have hA : MeasureTheory.Integrable (fun p : ℝ³ => (Work.OneBodyKin.boxHat ℓ (q - p)) ^ 2) :=
    integrable_boxHat_shift_sq hℓ q
  have hB : MeasureTheory.Integrable (fun p : ℝ³ => (Work.OneBodyKin.boxHat ℓ p) ^ 2) :=
    integrable_boxHat_sq hℓ
  have hC : MeasureTheory.Integrable (fun p : ℝ³ =>
      ((ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q) ^ 2) := by
    refine (hB.const_mul (((ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ q) ^ 2)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    show ((ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ q) ^ 2 * (Work.OneBodyKin.boxHat ℓ p) ^ 2
      = ((ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q) ^ 2
    ring
  have hmaj : MeasureTheory.Integrable (fun p : ℝ³ =>
      2 * (Work.OneBodyKin.boxHat ℓ (q - p)) ^ 2
        + 2 * ((ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q) ^ 2) :=
    (hA.const_mul 2).add (hC.const_mul 2)
  refine hmaj.mono' ((continuous_Bh_of_pos hℓ q).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have hb : (Bh ℓ q p) ^ 2
      = (Work.OneBodyKin.boxHat ℓ (q - p)
          - (ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q) ^ 2 := rfl
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hb]
  nlinarith [sq_nonneg (Work.OneBodyKin.boxHat ℓ (q - p)
    + (ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q)]

theorem integrable_momProj_Bh (ℓ d : ℝ) (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momProj ℓ d p * (Work.BoseKinLoc.Momentum.Bh ℓ q p) ^ 2) := by
  have hBsq : MeasureTheory.Integrable (fun p : ℝ³ => (Bh ℓ q p) ^ 2) :=
    integrable_Bh_sq hℓ q
  have hmom : Measurable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p) := by
    unfold Work.BoseKinLoc.momProj
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      measurable_const measurable_const
  refine hBsq.mono (hmom.aestronglyMeasurable.mul hBsq.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  have h0 : 0 ≤ (Bh ℓ q p) ^ 2 := sq_nonneg _
  have h1 : Work.BoseKinLoc.momProj ℓ d p ≤ 1 := by
    unfold Work.BoseKinLoc.momProj; split <;> norm_num
  have h2 : 0 ≤ Work.BoseKinLoc.momProj ℓ d p := by
    unfold Work.BoseKinLoc.momProj; split <;> norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h0), Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left h0 h1

end Work.BoseKinLoc.Momentum
