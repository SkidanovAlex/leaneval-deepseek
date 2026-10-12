import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.acube_axis_ftoc_c1
import Submission.Work.SmallBoxA0.fderiv_sineMode_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## the sine-carrying mode factor is smooth -/

/-- The factor `ψ(x) = (∏_{i ≠ m} u_{k i}(x i)) · sin ((k m π/s)(x m + s/2))` is smooth. -/
lemma sineModeBox_contDiff (s : ℝ) (m : Fin 3) (k : Fin 3 → ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ³ =>
      (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (x i)) *
        Real.sin (((k m : ℝ) * Real.pi / s) * (x m + s / 2))) := by
  unfold boxNeumann
  fun_prop

/-- Smooth functions are `C²` (the weakening used below). -/
lemma contDiff_two_of_contDiff_top {f : ℝ³ → ℝ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  h.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-! ## the integration-by-parts identity -/


theorem acube_mode_deriv_ibp_sine {s : ℝ} (hs : 0 < s) (m : Fin 3) (k : Fin 3 → ℕ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContDiff ℝ 2 g) :
    (∫ x in Submission.BoseGases.acube s,
        (fderiv ℝ g x (Submission.BoseGases.kcStdBasis m)) *
          ((∏ i ∈ Finset.univ.erase m, Submission.BoseGases.boxNeumann s (k i) (x i)) *
            Real.sin (((k m : ℝ) * Real.pi / s) * (x m + s / 2))))
      = -(((k m : ℝ) * Real.pi / s)) *
          (∫ x in Submission.BoseGases.acube s, g x * Submission.BoseGases.boxNeumann3 s k x) := by
  classical
  -- the sine-carrying mode factor
  set ψ : ℝ³ → ℝ := fun x =>
      (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (x i)) *
        Real.sin (((k m : ℝ) * Real.pi / s) * (x m + s / 2)) with hψ
  -- the test function whose `m`-th partial derivative we integrate
  set φ : ℝ³ → ℝ := fun x => g x * ψ x with hφ
  have hψ_cd : ContDiff ℝ ∞ ψ := by
    rw [hψ]
    exact sineModeBox_contDiff s m k
  have hψ2 : ContDiff ℝ 2 ψ := contDiff_two_of_contDiff_top hψ_cd
  have hφ_cd : ContDiff ℝ 1 φ := by
    rw [hφ]
    exact (hg.mul hψ2).of_le (by norm_num)
  -- `φ` vanishes on the two faces `z m = ±s/2`
  have hsin_pos : ∀ z : ℝ³, z m = s / 2 →
      Real.sin (((k m : ℝ) * Real.pi / s) * (z m + s / 2)) = 0 := by
    intro z hz
    rw [hz]
    have h1 : ((k m : ℝ) * Real.pi / s) * (s / 2 + s / 2) = ((k m : ℕ) : ℝ) * Real.pi := by
      field_simp
      ring
    rw [h1, Real.sin_nat_mul_pi]
  have hsin_neg : ∀ z : ℝ³, z m = -(s / 2) →
      Real.sin (((k m : ℝ) * Real.pi / s) * (z m + s / 2)) = 0 := by
    intro z hz
    rw [hz]
    have h1 : ((k m : ℝ) * Real.pi / s) * (-(s / 2) + s / 2) = 0 := by ring
    rw [h1, Real.sin_zero]
  have hfacep : ∀ z ∈ acube s, z m = s / 2 → φ z = 0 := by
    intro z _ hz
    have hz0 : ψ z = 0 := by
      rw [hψ]
      simp [hsin_pos z hz]
    rw [hφ]
    simp [hz0]
  have hfacen : ∀ z ∈ acube s, z m = -(s / 2) → φ z = 0 := by
    intro z _ hz
    have hz0 : ψ z = 0 := by
      rw [hψ]
      simp [hsin_neg z hz]
    rw [hφ]
    simp [hz0]
  have hP1 : (∫ z in acube s, fderiv ℝ φ z (kcStdBasis m)) = 0 :=
    acube_axis_ftoc_c1 hs m hφ_cd hfacep hfacen
  -- pointwise product rule
  have hpt : ∀ z : ℝ³, fderiv ℝ φ z (kcStdBasis m)
      = fderiv ℝ g z (kcStdBasis m) * ψ z + g z * fderiv ℝ ψ z (kcStdBasis m) := by
    intro z
    have hφ' : φ = g * ψ := by rw [hφ]; rfl
    rw [hφ']
    rw [fderiv_mul (hg.differentiable (by norm_num) z)
      (hψ_cd.differentiable (by simp) z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- the directional derivative of the sine-carrying factor
  have hψderiv : ∀ z : ℝ³, fderiv ℝ ψ z (kcStdBasis m)
      = ((k m : ℝ) * Real.pi / s) * boxNeumann3 s k z := by
    intro z
    rw [hψ]
    exact fderiv_sineMode_box hs m k z
  set A : ℝ³ → ℝ := fun z => fderiv ℝ g z (kcStdBasis m) * ψ z with hA
  set B : ℝ³ → ℝ := fun z => g z * fderiv ℝ ψ z (kcStdBasis m) with hB
  have hAc : Continuous A := by
    rw [hA]
    exact ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hψ_cd.continuous
  have hBc : Continuous B := by
    rw [hB]
    have h : (fun z : ℝ³ => g z * fderiv ℝ ψ z (kcStdBasis m))
        = fun z => g z * (((k m : ℝ) * Real.pi / s) * boxNeumann3 s k z) := by
      funext z
      rw [hψderiv z]
    rw [h]
    exact hg.continuous.mul (continuous_const.mul (by
      unfold boxNeumann3 boxNeumann
      fun_prop))
  have hAint : IntegrableOn A (acube s) :=
    ContinuousOn.integrableOn_compact (acube_compact hs) hAc.continuousOn
  have hBint : IntegrableOn B (acube s) :=
    ContinuousOn.integrableOn_compact (acube_compact hs) hBc.continuousOn
  have hAB : (∫ z in acube s, (A z + B z))
      = (∫ z in acube s, A z) + ∫ z in acube s, B z := integral_add hAint hBint
  have hrewrite : (∫ z in acube s, fderiv ℝ φ z (kcStdBasis m))
      = ∫ z in acube s, (A z + B z) :=
    integral_congr_ae (Eventually.of_forall (fun z => by
      rw [hA, hB]
      exact hpt z))
  have hBval : (∫ z in acube s, B z)
      = (((k m : ℝ) * Real.pi / s)) *
          (∫ z in acube s, g z * boxNeumann3 s k z) := by
    have h : B = fun z : ℝ³ => (((k m : ℝ) * Real.pi / s)) * (g z * boxNeumann3 s k z) := by
      rw [hB]
      funext z
      rw [hψderiv z]
      ring
    rw [h]
    rw [integral_const_mul]
  have h0 : (∫ z in acube s, A z)
      + (((k m : ℝ) * Real.pi / s)) * (∫ z in acube s, g z * boxNeumann3 s k z) = 0 := by
    rw [← hBval, ← hAB, ← hrewrite]
    exact hP1
  have hfin : (∫ z in acube s, A z)
      = -(((k m : ℝ) * Real.pi / s)) *
          (∫ z in acube s, g z * boxNeumann3 s k z) := by
    linarith
  exact hfin

end Work.SmallBoxA0
