import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Dirichlet word of a box-supported state with bounded partial derivatives

For a one-body state `h` vanishing off the centred box `acube ℓ` whose partial derivatives along
the coordinate directions are bounded by `D`,

    `bsDir h = Σ_k ∫_z (∂_k h z)² ≤ 3·D²·ℓ³`.

The point is that `acube ℓ` is **closed**, so off the box `h` agrees with `0` on a whole
neighbourhood of every point and hence `fderiv ℝ h z = 0` there; together with the pointwise bound
`(∂_k h z)² ≤ D²` on the box (of volume `ℓ³`) this bounds every one of the three integrals.

This is the `H¹` half of the box-supported a priori bounds for `bsShift` (the companion `L²` bound is
`bsL2_le_of_bounded_support`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

theorem bsDir_le_of_bounded_support {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 3)),
      |fderiv ℝ h z (Submission.BoseGases.kcStdBasis k)| ≤ D)
    (hzero : ∀ z ∉ Submission.BoseGases.acube ℓ, h z = 0) :
    Work.BSKinetic.Decomp.bsDir h ≤ 3 * (D ^ 2 * ℓ ^ 3) := by
  -- the volume of the box is finite, and equal to `ℓ³`
  have hvol : (volume : Measure ℝ³) (acube ℓ) ≠ ⊤ := by
    rw [acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_ne_top
  have hreal : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def, acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]
  -- off the closed box, `h` vanishes near every point, so its derivative vanishes
  have hzderiv : ∀ z ∉ acube ℓ, fderiv ℝ h z = 0 := by
    intro z hz
    have hopen : IsOpen (acube ℓ)ᶜ := (acube_isClosed ℓ).isOpen_compl
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen z hz
    have hev : h =ᶠ[𝓝 z] Function.const ℝ³ (0 : ℝ) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε, fun y hy => hzero y (hsub hy)⟩
    have h1 : fderiv ℝ h z = fderiv ℝ (Function.const ℝ³ (0 : ℝ)) z :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
    have h0 : fderiv ℝ (Function.const ℝ³ (0 : ℝ)) z = 0 := by
      rw [fderiv_const]; rfl
    exact h1.trans h0
  -- each of the three coordinate integrals is bounded by `D²·|acube ℓ|`
  have hterm : ∀ k : Fin 3,
      ∫ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2 ≤ D ^ 2 * ℓ ^ 3 := by
    intro k
    have hpt : ∀ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2
        ≤ (acube ℓ).indicator (fun _ => D ^ 2) z := by
      intro z
      by_cases hzc : z ∈ acube ℓ
      · rw [Set.indicator_of_mem hzc]
        exact sq_le_sq' (abs_le.mp (hb k z)).1 (abs_le.mp (hb k z)).2
      · rw [Set.indicator_of_notMem hzc, hzderiv z hzc]
        simp
    have hgint : Integrable (fun z : ℝ³ => (acube ℓ).indicator (fun _ => D ^ 2) z) := by
      have h1 : Integrable (fun _ : ℝ³ => D ^ 2) (volume.restrict (acube ℓ)) := by
        rw [integrable_const_iff]
        exact Or.inr (isFiniteMeasure_restrict.mpr hvol)
      exact (integrable_indicator_iff (acube_measurable ℓ)).mpr h1
    calc ∫ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2
        ≤ ∫ z : ℝ³, (acube ℓ).indicator (fun _ => D ^ 2) z :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) hgint
            (Filter.Eventually.of_forall hpt)
      _ = D ^ 2 * ℓ ^ 3 := by
          rw [integral_indicator_const (D ^ 2) (acube_measurable ℓ), hreal, smul_eq_mul]
          ring
  calc Work.BSKinetic.Decomp.bsDir h
      = ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2 := rfl
    _ ≤ ∑ _k : Fin 3, D ^ 2 * ℓ ^ 3 := Finset.sum_le_sum fun k _ => hterm k
    _ = 3 * (D ^ 2 * ℓ ^ 3) := by
        rw [Fin.sum_univ_three]
        ring

end Work.BSKinetic.Decomp
