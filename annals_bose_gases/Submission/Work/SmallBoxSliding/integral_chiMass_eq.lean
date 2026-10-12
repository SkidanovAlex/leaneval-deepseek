import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.Sliding
import Submission.Work.SmallBoxSliding.nBox_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normalisation of the sliding `χ_{B(u)}`-mass

We compute the `u`-integral of the per-box `χ_{B(u)}²`-mass
(`Work.SmallBoxSliding.chiMass`)

    ∫_u chiMass M ℓ d u = ∫_u ∫_x χ_{B(u)}(x)² dx du = ℓ³ ,

which is the `nBox_integral_u` normalisation read at the cutoff: the two
factors of `χ_{B(u)}(x) = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` separate, the
`u`-integral of the second factor is `∫χ_M² = 1` by translation invariance
(`Submission.BoseGases.chiSmall_L2`), and the remaining `x`-integral of
`χ_M(x/ℓ)²` is `ℓ³` by the additive-Haar dilation formula
(`MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg`) in dimension `3`.

The only substance beyond those two normalisations is Fubini, for which the
joint integrability of `(u,x) ↦ χ_{B(u)}(x)²` is obtained from
`MeasureTheory.integrable_prod_iff`: the `x`-slice is continuous with support
in the fixed big-box ball (`Submission.BoseGases.chiSmallB_support_big_box`),
and the `u`-marginal norm integral is exactly
`Work.SmallBoxSliding.integrable_chiSmallB_mass`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option linter.unusedVariables false

/-! ## The two one-factor normalisations -/

/-- Translation invariance of the `χ_M²` mass: for every centre `y`,
`∫_u χ_M(y − u)² du = ∫ χ_M² = 1`. -/
lemma integral_chiSmall_sub_sq_eq_one {M : ℕ} (hM : 1 ≤ M) (y : ℝ³) :
    (∫ u : ℝ³, (chiSmall M (y - u)) ^ 2) = 1 := by
  rw [integral_sub_left_eq_self (fun v : ℝ³ => (chiSmall M v) ^ 2) volume y, chiSmall_L2 hM]

/-- The additive-Haar dilation normalisation: `∫_x χ_M(x/ℓ)² dx = ℓ³`.
This is `integral_comp_inv_smul_of_nonneg` together with `∫χ_M² = 1` and
`finrank ℝ ℝ³ = 3`. -/
lemma integral_chiSmall_inv_smul_sq {M : ℕ} (hM : 1 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : ℝ³, (chiSmall M (ℓ⁻¹ • x)) ^ 2) = ℓ ^ 3 := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℝ³)
      (fun z : ℝ³ => (chiSmall M z) ^ 2) (R := ℓ) (le_of_lt hℓ)
  rw [show ℓ ^ Module.finrank ℝ ℝ³ = ℓ ^ 3 by rw [finrank_euclideanSpace]; norm_num] at h
  rw [h, chiSmall_L2 hM, smul_eq_mul, mul_one]

/-! ## Joint integrability of the two-factor cutoff, for Fubini -/

/-- The `x`-slice of the two-factor cutoff square is integrable for every `u`:
it is continuous and supported in the fixed big-box ball `‖x‖ ≤ √3·ℓ/2`
(`chiSmallB_support_big_box`). -/
lemma integrable_chiSmallB_sq_slice {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ³) : Integrable (fun x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2) := by
  have hcont : Continuous (fun x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2) := by
    have h1 : Continuous (fun x : ℝ³ => chiScale ℓ x) :=
      (chiScale_continuous ℓ)
    have h2 : Continuous (fun x : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
      (chiSmall_continuous hM).comp ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const)
    have h3 : Continuous (fun x : ℝ³ => chiSmallB M ℓ d u x) := by
      have hgoal : (fun x : ℝ³ => chiSmallB M ℓ d u x)
          = fun x : ℝ³ => chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u) := rfl
      rw [hgoal]
      exact h1.mul h2
    exact h3.pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2))) (isCompact_closedBall _ _) ?_
  intro x hx
  have hx' : chiSmallB M ℓ d u x ≠ 0 := by
    intro h0
    exact hx (by simp [h0])
  have hcoord : ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2 := fun j => chiSmallB_support_big_box hM hℓ hx' j
  have hnorm : ‖x‖ ≤ Real.sqrt 3 * (ℓ / 2) := coord_box_subset_eucl_ball (by positivity) hcoord
  simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hnorm

/-- **Joint integrability of `(u,x) ↦ χ_{B(u)}(x)²`** on `ℝ³ × ℝ³` (product
Lebesgue measure), the hypothesis of Fubini in the main computation.  Proved
through `MeasureTheory.integrable_prod_iff`: the function is continuous, every
`x`-slice is integrable (`integrable_chiSmallB_sq_slice`) and the `u`-marginal
norm integral is the known integrable mass `integrable_chiSmallB_mass`. -/
lemma uncurry_chiSmallB_sq_integrable {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) :
    Integrable (Function.uncurry (fun u x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2))
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ³ × ℝ³ => (chiSmallB M ℓ d p.1 p.2) ^ 2) := by
    have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
      (chiScale_continuous ℓ).comp continuous_snd
    have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
      (chiSmall_continuous hM).comp ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
    have h3 : Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
      have hgoal : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
          = fun p : ℝ³ × ℝ³ => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
      rw [hgoal]
      exact h1.mul h2
    exact h3.pow 2
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun u x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2)) (volume.prod volume) :=
    hcont.aestronglyMeasurable
  rw [integrable_prod_iff (μ := volume) (ν := volume) hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with u
    exact integrable_chiSmallB_sq_slice hM hℓ u
  · have heq : (fun u : ℝ³ =>
        ∫ x, ‖(Function.uncurry (fun u x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2)) (u, x)‖)
        = (fun u : ℝ³ => ∫ x, (chiSmallB M ℓ d u x) ^ 2) := by
      funext u
      refine integral_congr_ae (ae_of_all _ (fun x => ?_))
      simp only [Function.uncurry_apply_pair]
      exact abs_of_nonneg (sq_nonneg (chiSmallB M ℓ d u x))
    rw [heq]
    exact integrable_chiSmallB_mass hM hℓ hd

/-! ## The normalisation of the sliding mass -/

/-- **The `u`-integral of the sliding `χ_{B(u)}²`-mass is the big-box volume**:
`∫_u chiMass M ℓ d u = ℓ³`. -/
theorem integral_chiMass_eq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.chiMass M ℓ d u) = ℓ ^ 3 := by
  -- Fubini: swap the `u`- and `x`-integrations.
  have hFub := MeasureTheory.integral_integral_swap (μ := volume) (ν := volume)
    (f := fun u x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2) (uncurry_chiSmallB_sq_integrable hM hℓ hd)
  have hswap : (∫ u : ℝ³, chiMass M ℓ d u) = ∫ x : ℝ³, ∫ u : ℝ³, (chiSmallB M ℓ d u x) ^ 2 := by
    rw [show (∫ u : ℝ³, chiMass M ℓ d u)
        = ∫ u : ℝ³, ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2 by simp only [chiMass_def]]
    exact hFub
  rw [hswap]
  -- the `u`-integral of each slice is `χ_M(x/ℓ)²` (translation invariance).
  have hinner : (∫ x : ℝ³, ∫ u : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
      = ∫ x : ℝ³, (chiScale ℓ x) ^ 2 := by
    refine integral_congr_ae (ae_of_all _ (fun x => ?_))
    change (∫ u : ℝ³, (chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
      = (chiScale ℓ x) ^ 2
    have h : (fun u : ℝ³ => (chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
        = (fun u : ℝ³ => (chiScale ℓ x) ^ 2 * (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2) := by
      funext u
      rw [mul_pow]
    rw [h, integral_const_mul, integral_chiSmall_sub_sq_eq_one hM ((ℓ * d)⁻¹ • x), mul_one]
  rw [hinner]
  -- the dilation normalisation (corpus bump)
  exact Submission.BoseGases.integral_chiScale_sq hℓ

end Work.SmallBoxSliding
