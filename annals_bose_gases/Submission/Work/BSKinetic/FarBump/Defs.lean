import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BSKinetic.FarBump.Defs`

The concrete objects of the far-bump witness used by
`Work.BSKinetic.Decomp.bsOneBody_farBump_pos` and its siblings.

With `e₀ = kcStdBasis 0`, `u = 3 • e₀` and `z₀ = ℓ • u = farShift ℓ`:

* `farPsi ℓ δ = slotFun1 (farBump ℓ δ)` is the bump `z ↦ χ(δ⁻¹ • (z − z₀))`, centred at `z₀`,
  of support radius `δ/2`;
* `farWin ℓ = bsWin ℓ u` is the window `z ↦ χ_ℓ(z − z₀)` of the moving box `Λ(u) = ℓu + acube ℓ`;
* `farMu ℓ δ = ⨍_{Λ(u)} farPsi ℓ δ` is the box mean of the bump over the moving box;
* `farPhi ℓ δ = farWin ℓ · (farPsi ℓ δ − farMu ℓ δ)` is the windowed, box-mean-free state whose
  kinetic form is `bsOneBody ℓ F u (slotFun1 (farBump ℓ δ))` (`bsOneBody_farBump_eq`).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real ENNReal BigOperators

namespace Work.BSKinetic.FarBump

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The objects -/

/-- The centre `z₀ = ℓ • (3 • e₀) = ℓu` of the far bump. -/
def farShift (ℓ : ℝ) : ℝ³ := ℓ • ((3 : ℝ) • kcStdBasis 0)

/-- The far bump `ψ_δ(z) = χ(δ⁻¹ • (z − z₀))`, as a function of the position. -/
def farPsi (ℓ δ : ℝ) : ℝ³ → ℝ := fun z => chi (δ⁻¹ • (z - farShift ℓ))

/-- The window `χ_u(z) = χ_ℓ(z − z₀)` of the moving box at `u = 3e₀`. -/
def farWin (ℓ : ℝ) : ℝ³ → ℝ := fun z => chiScale ℓ (z - farShift ℓ)

/-- The box mean `⨍_{Λ(u)}ψ_δ` of the far bump over the moving box `Λ(u) = ℓu + acube ℓ`. -/
def farMu (ℓ δ : ℝ) : ℝ :=
  Work.BSKinetic.bsMean ℓ ((3 : ℝ) • kcStdBasis 0) (farPsi ℓ δ)

/-- The windowed, mean-free far bump: `χ_u·(ψ_δ − ⨍_{Λ(u)}ψ_δ)`. -/
def farPhi (ℓ δ : ℝ) : ℝ³ → ℝ := fun z => farWin ℓ z * (farPsi ℓ δ z - farMu ℓ δ)

/-! ## 2. Identifications with the corpus vocabulary -/

lemma farWin_eq_bsWin (ℓ : ℝ) :
    farWin ℓ = Work.BSKinetic.bsWin ℓ ((3 : ℝ) • kcStdBasis 0) := rfl

lemma farShift_eq' (ℓ : ℝ) : farShift ℓ = (3 * ℓ) • kcStdBasis 0 := by
  rw [farShift, mul_smul, smul_comm]

/-- The far bump is the slot-`0` function of the corpus's `farBump` state. -/
lemma farPsi_eq_slotFun1 (ℓ δ : ℝ) :
    farPsi ℓ δ = Work.BSKinetic.slotFun1 (Work.BSKinetic.farBump ℓ δ) := by
  funext z
  simp only [farPsi, farShift, Work.BSKinetic.slotFun1, Work.BSKinetic.farBump]
  congr 2
  rw [mul_smul, smul_comm]

/-- The box mean of the far bump reduces to the scaled integral over the centred cube. -/
lemma bsMean_farPsi (ℓ δ : ℝ) :
    Work.BSKinetic.bsMean ℓ ((3 : ℝ) • kcStdBasis 0) (farPsi ℓ δ)
      = (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, chi (δ⁻¹ • w) := by
  simp only [Work.BSKinetic.bsMean, farPsi]
  congr 1
  refine setIntegral_congr_fun (acube_measurable ℓ) (fun w _ => ?_)
  simp only [farShift]
  congr 1
  rw [add_sub_cancel_left]

/-! ## 3. Smoothness, support and sign -/

lemma farPsi_nonneg (ℓ δ : ℝ) : 0 ≤ farPsi ℓ δ := fun z => chi_nonneg _

lemma farWin_nonneg (ℓ : ℝ) : 0 ≤ farWin ℓ := fun z => chiScale_nonneg _ _

lemma farPsi_contDiff (ℓ : ℝ) {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ (⊤ : ENat) (farPsi ℓ δ) := by
  unfold farPsi
  exact chi_contDiff.comp (by fun_prop)

lemma farWin_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) : ContDiff ℝ (⊤ : ENat) (farWin ℓ) := by
  unfold farWin
  exact (chiScale_contDiff (ne_of_gt hℓ)).comp (by fun_prop)

lemma farPsi_hasCompactSupport (ℓ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (farPsi ℓ δ) := by
  unfold farPsi
  let φ : ℝ³ ≃ₜ ℝ³ := (Homeomorph.subRight (farShift ℓ)).trans
    (Homeomorph.smulOfNeZero (δ⁻¹) (inv_ne_zero (ne_of_gt hδ)))
  convert chi_hasCompactSupport.comp_homeomorph φ using 1
  ext z
  simp [φ, Homeomorph.trans, Homeomorph.subRight, Homeomorph.smulOfNeZero]

lemma farWin_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) : HasCompactSupport (farWin ℓ) := by
  unfold farWin
  let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.subRight (farShift ℓ)
  convert (chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph φ using 1
  ext z
  simp [φ, Homeomorph.subRight]

/-- The far bump vanishes off the ball of radius `δ/2` around `z₀`. -/
lemma farPsi_eq_zero_of_norm_gt {ℓ δ : ℝ} (hδ : 0 < δ) {z : ℝ³}
    (hz : δ / 2 < ‖z - farShift ℓ‖) : farPsi ℓ δ z = 0 := by
  refine chi_eq_zero_of_norm_gt _ ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ), inv_mul_eq_div]
  rw [lt_div_iff₀ hδ]
  linarith

/-- The support of the far bump is contained in the ball of radius `δ/2` around `z₀`. -/
lemma farPsi_support_le {ℓ δ : ℝ} (hδ : 0 < δ) {z : ℝ³} (hz : farPsi ℓ δ z ≠ 0) :
    ‖z - farShift ℓ‖ ≤ δ / 2 := by
  by_contra h
  exact hz (farPsi_eq_zero_of_norm_gt hδ (lt_of_not_ge h))

/-- The window is bounded by `(√chiNormSq)⁻¹`. -/
lemma farWin_le (ℓ : ℝ) (z : ℝ³) : farWin ℓ z ≤ (Real.sqrt chiNormSq)⁻¹ := by
  calc farWin ℓ z = chiScale ℓ (z - farShift ℓ) := rfl
    _ ≤ |chiScale ℓ (z - farShift ℓ)| := le_abs_self _
    _ ≤ (Real.sqrt chiNormSq)⁻¹ := abs_chiScale_le ℓ _

lemma farMu_nonneg {ℓ δ : ℝ} (hℓ : 0 < ℓ) : 0 ≤ farMu ℓ δ := by
  rw [farMu, bsMean_farPsi]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hℓ) 3))
    (integral_nonneg (fun w => chi_nonneg _))

lemma farWin_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) : Continuous (farWin ℓ) :=
  (farWin_contDiff hℓ).continuous

lemma farPsi_continuous (ℓ : ℝ) {δ : ℝ} (hδ : 0 < δ) : Continuous (farPsi ℓ δ) :=
  (farPsi_contDiff ℓ hδ).continuous

lemma farPhi_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ENat) (farPhi ℓ δ) :=
  (farWin_contDiff hℓ).mul ((farPsi_contDiff ℓ hδ).sub contDiff_const)

lemma farPhi_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) (δ : ℝ) :
    HasCompactSupport (farPhi ℓ δ) :=
  (farWin_hasCompactSupport hℓ).mul_right

/-! ## 4. The identification of the `N = 1` kinetic form -/

/-- **The one-body kinetic form at the far bump is the `farPhi`-form**: the `bsOneBody` integrand
is `kinFT` of the complexification of `farPhi ℓ δ`. -/
lemma bsOneBody_farBump_eq (ℓ δ c : ℝ) :
    Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) ((3 : ℝ) • kcStdBasis 0)
        (Work.BSKinetic.slotFun1 (Work.BSKinetic.farBump ℓ δ))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          fsKinCoeff c ‖p‖ * ‖kinFT (fun z : ℝ³ => (farPhi ℓ δ z : ℂ)) p‖ ^ 2 := by
  rw [Work.BSKinetic.bsOneBody]
  congr 2
  have h : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ ((3 : ℝ) • kcStdBasis 0) z : ℂ) *
        (Work.BSKinetic.bsQ ℓ ((3 : ℝ) • kcStdBasis 0)
          (Work.BSKinetic.slotFun1 (Work.BSKinetic.farBump ℓ δ)) z : ℂ))
      = (fun z : ℝ³ => (farPhi ℓ δ z : ℂ)) := by
    funext z
    simp only [farPhi, farMu, Work.BSKinetic.bsQ, farWin_eq_bsWin, farPsi_eq_slotFun1,
      Complex.ofReal_mul]
  rw [h]

end Work.BSKinetic.FarBump
