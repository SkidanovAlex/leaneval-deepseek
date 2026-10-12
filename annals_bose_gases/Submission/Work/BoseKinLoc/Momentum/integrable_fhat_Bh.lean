import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BoseKinLoc.Momentum.momDefs
import Submission.Work.BoseKinLoc.Momentum.sm_cubFT
import Submission.Work.OneBodyKin.BoxHat.boxHat_scale
import Submission.Work.OneBodyKin.SymAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integrable_fhat_Bh`

The sliding symbol

  `Bh ℓ q p = θ̂_ℓ(q − p) − ℓ⁻³ θ̂_ℓ p · θ̂_ℓ q`

of FS `eq:Q1Qslide` is bounded (by `2ℓ³` for `ℓ > 0`, and is *identically zero* for `ℓ ≤ 0`,
where the cube `acube ℓ` is null).  Since `‖fhat ψ‖²` is integrable for a smooth compactly
supported `ψ` (`Work.BSKinetic.integrable_kinFT_sq`), the product

  `q ↦ ‖fhat ψ q‖² · Bh ℓ q p²`

is integrable: it is dominated by the constant multiple `(2ℓ³)² ‖fhat ψ q‖²` of an integrable
function, and it is measurable because `q ↦ Bh ℓ q p` is continuous (via the scaling law
`boxHat ℓ q = ℓ³ · cubFT (ℓ • q)` of the profile).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `boxHat 1` is the unit-cube symbol `cubFT` of this chapter (both are
`∫_{acube 1} cos⟪q,x⟫ dx`). -/
lemma boxHat_one_eq_cubFT (q : ℝ³) : Work.OneBodyKin.boxHat 1 q = cubFT q := rfl

/-- For `ℓ > 0` the box profile `q ↦ boxHat ℓ q` is continuous.  This follows from the scaling
law `boxHat ℓ q = ℓ³ · boxHat 1 (ℓ • q)` (`Work.OneBodyKin.BoxHat.boxHat_scale`) and continuity
of the unit-cube symbol (`cubFT_continuous`). -/
lemma continuous_boxHat_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun q : ℝ³ => Work.OneBodyKin.boxHat ℓ q) := by
  have hfun : (fun q : ℝ³ => ℓ ^ 3 * cubFT (ℓ • q))
      = fun q : ℝ³ => Work.OneBodyKin.boxHat ℓ q := by
    funext q
    rw [← boxHat_one_eq_cubFT]
    exact (Work.OneBodyKin.BoxHat.boxHat_scale hℓ q).symm
  rw [← hfun]
  exact continuous_const.mul (cubFT_continuous.comp (continuous_const_smul ℓ))

/-- **The sliding symbol is bounded.**  For `ℓ > 0`, `|Bh ℓ q p| ≤ 2ℓ³`. -/
lemma abs_Bh_le {ℓ : ℝ} (hℓ : 0 < ℓ) (q p : ℝ³) : |Bh ℓ q p| ≤ 2 * ℓ ^ 3 := by
  have hℓ3pos : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hb : ∀ r : ℝ³, |Work.OneBodyKin.boxHat ℓ r| ≤ ℓ ^ 3 :=
    fun r => Work.OneBodyKin.abs_boxHat_le hℓ.le r
  have hprod : |(ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q|
      ≤ ℓ ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (ℓ ^ 3)⁻¹)]
    calc (ℓ ^ 3)⁻¹ * |Work.OneBodyKin.boxHat ℓ p| * |Work.OneBodyKin.boxHat ℓ q|
        ≤ (ℓ ^ 3)⁻¹ * ℓ ^ 3 * ℓ ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hb p) (by positivity)) (hb q)
            (abs_nonneg _) (by positivity)
      _ = ℓ ^ 3 := by rw [inv_mul_cancel₀ (ne_of_gt hℓ3pos), one_mul]
  calc |Bh ℓ q p|
      = |Work.OneBodyKin.boxHat ℓ (q - p)
          - (ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q| := rfl
    _ ≤ |Work.OneBodyKin.boxHat ℓ (q - p)|
          + |(ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q| :=
        abs_sub _ _
    _ ≤ ℓ ^ 3 + ℓ ^ 3 := add_le_add (hb (q - p)) hprod
    _ = 2 * ℓ ^ 3 := by ring

/-- `‖fhat ψ q‖²` is integrable for a smooth compactly supported `ψ`. -/
lemma integrable_norm_sq_fhat (ψ : ℝ³ → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Integrable (fun q : ℝ³ => ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2) := by
  simpa [Work.BoseKinLoc.fhat] using Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs

theorem integrable_fhat_Bh (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (Work.BoseKinLoc.Momentum.Bh ℓ q p) ^ 2) := by
  have hintf : Integrable (fun q : ℝ³ => ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2) :=
    integrable_norm_sq_fhat ψ hψ hcs
  rcases le_or_gt ℓ 0 with hℓ | hℓ
  · -- `ℓ ≤ 0`: the cube `acube ℓ` is null, hence `boxHat ℓ` — and therefore `Bh ℓ · p` —
    -- vanishes identically.
    have hsub : acube ℓ ⊆ acube 0 := by
      intro y hy m
      have h1 : y m ≤ ℓ / 2 := (hy m).2
      have h2 : -ℓ / 2 ≤ y m := (hy m).1
      have h3 : y m = 0 := by linarith
      simp [h3]
    have hzero : volume (acube ℓ : Set ℝ³) = 0 := by
      have h : volume (acube 0 : Set ℝ³) = 0 := by
        rw [acube_volume 0 le_rfl]
        simp
      exact measure_mono_null hsub h
    have hbox : ∀ r : ℝ³, Work.OneBodyKin.boxHat ℓ r = 0 := by
      intro r
      simp only [Work.OneBodyKin.boxHat]
      rw [setIntegral_measure_zero _ hzero]
    have hBh : ∀ q : ℝ³, Bh ℓ q p = 0 := by
      intro q
      simp only [Bh, hbox, mul_zero, sub_zero]
    refine Integrable.congr (integrable_zero ℝ³ ℝ volume)
      (Filter.Eventually.of_forall fun q => ?_)
    simp [hBh q]
  · -- `ℓ > 0`: `Bh ℓ · p` is continuous and bounded by `2ℓ³`, and `‖fhat ψ‖²` is integrable.
    have hcont : Continuous (fun q : ℝ³ => Work.OneBodyKin.boxHat ℓ q) :=
      continuous_boxHat_of_pos hℓ
    have hcontBh : Continuous (fun q : ℝ³ => Bh ℓ q p) := by
      have h1 : Continuous (fun q : ℝ³ => Work.OneBodyKin.boxHat ℓ (q - p)) :=
        hcont.comp (continuous_id.sub continuous_const)
      have h2 : Continuous
          (fun q : ℝ³ => (ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p
            * Work.OneBodyKin.boxHat ℓ q) :=
        hcont.const_mul ((ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p)
      exact h1.sub h2
    have haesm : AEStronglyMeasurable
        (fun q : ℝ³ => ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2) volume :=
      hintf.aestronglyMeasurable.mul (hcontBh.pow 2).aestronglyMeasurable
    have hbound : ∀ q : ℝ³,
        ‖‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2‖
          ≤ ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (2 * ℓ ^ 3) ^ 2 := by
      intro q
      have hsq : (Bh ℓ q p) ^ 2 ≤ (2 * ℓ ^ 3) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ 3)]
        exact abs_Bh_le hℓ q p
      have hnorm : ‖‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2‖
          = ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    exact (hintf.mul_const ((2 * ℓ ^ 3) ^ 2)).mono' haesm
      (Filter.Eventually.of_forall hbound)

end Work.BoseKinLoc.Momentum
