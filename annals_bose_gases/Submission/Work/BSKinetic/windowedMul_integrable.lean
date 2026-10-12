import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Auxiliary facts about directional derivatives of smooth functions -/

/-- The directional derivative `x ↦ ∂_v f x` of a smooth function is again smooth. -/
lemma contDiff_fderiv_apply {f : ℝ³ → ℝ} (hf : ContDiff ℝ (⊤ : ENat) f) (v : ℝ³) :
    ContDiff ℝ (⊤ : ENat) (fun x : ℝ³ => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp (hf.fderiv_right (m := (⊤ : ENat)) (by simp))

/-- The directional derivative `x ↦ ∂_v f x` of a smooth function is continuous. -/
lemma continuous_fderiv_apply {f : ℝ³ → ℝ} (hf : ContDiff ℝ (⊤ : ENat) f) (v : ℝ³) :
    Continuous (fun x : ℝ³ => fderiv ℝ f x v) :=
  (contDiff_fderiv_apply hf v).continuous

/-! ## Integrating products with a compactly supported factor -/

/-- A product of a continuous compactly supported function with a continuous function is
integrable on `ℝ³`. -/
lemma integrable_mul_of_hasCompactSupport {A B : ℝ³ → ℝ} (hA : Continuous A)
    (hB : Continuous B) (hcsA : HasCompactSupport A) :
    Integrable (fun x : ℝ³ => A x * B x) :=
  (hA.mul hB).integrable_of_hasCompactSupport hcsA.mul_right

/-- Transport of integrability along a pointwise equality. -/
lemma integrable_congr_pointwise {f g : ℝ³ → ℝ} (hg : Integrable g) (h : ∀ x, g x = f x) :
    Integrable f :=
  hg.congr (Filter.EventuallyEq.of_eq (funext h))

theorem windowedMul_integrable {χ F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ)
    (hF : ContDiff ℝ (⊤ : ENat) F) (k : Fin 3) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2)
    ∧ MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        2 * (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) * χ x * F x
          * (fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)))
    ∧ MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (χ x) ^ 2 * (fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) ^ 2)
    ∧ MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (χ x) ^ 2 * F x
          * (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
              fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
              (Submission.BoseGases.kcStdBasis k)))
    ∧ MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * F y) x
          (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  -- abbreviations for the directional derivatives occurring in the statement
  have hAχ : Continuous (fun x : ℝ³ => fderiv ℝ χ x (kcStdBasis k)) :=
    continuous_fderiv_apply hχ (kcStdBasis k)
  have hcsAχ : HasCompactSupport (fun x : ℝ³ => fderiv ℝ χ x (kcStdBasis k)) :=
    hcs.fderiv_apply ℝ (kcStdBasis k)
  have hAF : Continuous (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) :=
    continuous_fderiv_apply hF (kcStdBasis k)
  have hA2F : Continuous (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ F y (kcStdBasis k)) x (kcStdBasis k)) :=
    continuous_fderiv_apply (contDiff_fderiv_apply hF (kcStdBasis k)) (kcStdBasis k)
  have hχF : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => χ y * F y) := hχ.mul hF
  have hAχF : Continuous (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => χ y * F y) x (kcStdBasis k)) :=
    continuous_fderiv_apply hχF (kcStdBasis k)
  have hcsAχF : HasCompactSupport (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => χ y * F y) x (kcStdBasis k)) :=
    (hcs.mul_right).fderiv_apply ℝ (kcStdBasis k)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `(∂_k χ)² F²`
    have hB : Continuous (fun x : ℝ³ =>
        fderiv ℝ χ x (kcStdBasis k) * (F x * F x)) :=
      hAχ.mul (hF.continuous.mul hF.continuous)
    refine integrable_congr_pointwise
      (integrable_mul_of_hasCompactSupport (A := fun x : ℝ³ => fderiv ℝ χ x (kcStdBasis k))
        (B := fun x : ℝ³ => fderiv ℝ χ x (kcStdBasis k) * (F x * F x)) hAχ hB hcsAχ) ?_
    intro x
    ring
  · -- `2 (∂_k χ) χ F (∂_k F)`
    have hB : Continuous (fun x : ℝ³ => 2 * χ x * F x * (fderiv ℝ F x (kcStdBasis k))) :=
      (((continuous_const : Continuous fun _ : ℝ³ => (2 : ℝ)).mul hχ.continuous).mul
        hF.continuous).mul hAF
    refine integrable_congr_pointwise
      (integrable_mul_of_hasCompactSupport (A := fun x : ℝ³ => fderiv ℝ χ x (kcStdBasis k))
        (B := fun x : ℝ³ => 2 * χ x * F x * (fderiv ℝ F x (kcStdBasis k)))
        hAχ hB hcsAχ) ?_
    intro x
    ring
  · -- `χ² (∂_k F)²`
    have hB : Continuous (fun x : ℝ³ => χ x * (fderiv ℝ F x (kcStdBasis k)) ^ 2) :=
      hχ.continuous.mul ((hAF).pow 2)
    refine integrable_congr_pointwise
      (integrable_mul_of_hasCompactSupport (A := χ)
        (B := fun x : ℝ³ => χ x * (fderiv ℝ F x (kcStdBasis k)) ^ 2) hχ.continuous hB hcs) ?_
    intro x
    ring
  · -- `χ² F ∂_k∂_k F`
    have hB : Continuous (fun x : ℝ³ => χ x * (F x *
        fderiv ℝ (fun y : ℝ³ => fderiv ℝ F y (kcStdBasis k)) x (kcStdBasis k))) :=
      hχ.continuous.mul (hF.continuous.mul hA2F)
    refine integrable_congr_pointwise
      (integrable_mul_of_hasCompactSupport (A := χ)
        (B := fun x : ℝ³ => χ x * (F x *
          fderiv ℝ (fun y : ℝ³ => fderiv ℝ F y (kcStdBasis k)) x (kcStdBasis k)))
        hχ.continuous hB hcs) ?_
    intro x
    ring
  · -- `(∂_k (χ F))²`
    refine integrable_congr_pointwise
      (integrable_mul_of_hasCompactSupport
        (A := fun x : ℝ³ => fderiv ℝ (fun y : ℝ³ => χ y * F y) x (kcStdBasis k))
        (B := fun x : ℝ³ => fderiv ℝ (fun y : ℝ³ => χ y * F y) x (kcStdBasis k))
        hAχF hAχF hcsAχF) ?_
    intro x
    ring

end Work.BSKinetic
