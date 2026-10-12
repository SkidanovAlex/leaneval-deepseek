import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The Leibniz formula for the big-box window** applied to a one-body state on `ℝ³`.
Writing `bsWin ℓ u y = chiScale ℓ (y − ℓ•u)`, the derivative of the windowed product
`y ↦ bsWin ℓ u y * ψ y` along a direction `e` is

    `∂_e (bsWin ℓ u · ψ)(x) = chiScale ℓ (x − ℓ•u) · ∂_eψ(x)
        + ψ(x) · ∂_e(chiScale ℓ)(x − ℓ•u)`.

The two `u`-dependent factors are the *same* bump `chiScale ℓ` at the sliding point `x − ℓ•u`. -/
lemma fderiv_bsWin_mul_apply {ℓ : ℝ} (u x : ℝ³) (e : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x e
      = chiScale ℓ (x - ℓ • u) * fderiv ℝ ψ x e
        + ψ x * fderiv ℝ (chiScale ℓ) (x - ℓ • u) e := by
  have hwin : DifferentiableAt ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) x := by
    have h1 : (fun y : ℝ³ => chiScale ℓ (y - ℓ • u))
        = chiScale ℓ ∘ (fun y : ℝ³ => y - ℓ • u) := rfl
    rw [h1]
    exact ((Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any ℓ).differentiable
      (by norm_num) (x - ℓ • u)).comp x (by fun_prop)
  have hfun : (fun y : ℝ³ => bsWin ℓ u y * ψ y)
      = (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) * ψ := by
    funext y; rfl
  rw [hfun, fderiv_mul hwin hψ, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    Work.UBBInputs9.B.ChiDeriv.fderiv_chiScale_comp_sub_const]

theorem integral_bsWin_deriv_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (x : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    ∫ u : EuclideanSpace ℝ (Fin 3), (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsWin ℓ u y * ψ y) x (Submission.BoseGases.kcStdBasis k)) ^ 2
      = (fderiv ℝ ψ x (Submission.BoseGases.kcStdBasis k)) ^ 2
        + ((∫ z : EuclideanSpace ℝ (Fin 3), (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 3) * (ψ x) ^ 2 := by
  have hψdiff : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
  have hpt : ∀ u : ℝ³,
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2
        = ((fderiv ℝ ψ x (kcStdBasis k)) * chiScale ℓ (x - ℓ • u)
            + (ψ x) * fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) ^ 2 := by
    intro u
    rw [fderiv_bsWin_mul_apply u x (kcStdBasis k) hψdiff]
    ring
  have hQval : (∫ u : ℝ³, (fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) ^ 2)
      = (∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3 := by
    rw [Work.UBBInputs9.B.integral_fderiv_chiScale_sub_smul_sq ℓ hℓ x (kcStdBasis k),
      Work.UBBInputs9.B.integral_fderiv_chiScale_sq ℓ hℓ (kcStdBasis k)]
    rw [div_eq_div_iff (pow_ne_zero 2 (ne_of_gt hℓ)) (pow_ne_zero 3 (ne_of_gt hℓ))]
    ring
  have hmain := Work.UBBInputs9.B.integral_sq_add_eq (fderiv ℝ ψ x (kcStdBasis k)) (ψ x)
    ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
    (P := fun u : ℝ³ => chiScale ℓ (x - ℓ • u))
    (Q := fun u : ℝ³ => fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k))
    (Work.UBBInputs9.B.integrable_chiScale_sub_smul_sq ℓ hℓ x)
    (Work.UBBInputs9.B.integrable_chiScale_sub_smul_mul_fderiv ℓ hℓ x (kcStdBasis k))
    (Work.UBBInputs9.C.integrable_partialDeriv_chiScale_sub_smul ℓ hℓ x k)
    (Work.UBBInputs9.B.integral_chiScale_sub_smul_sq ℓ hℓ x)
    (Work.UBBInputs9.B.integral_chiScale_sub_smul_mul_fderiv_eq_zero ℓ hℓ x (kcStdBasis k))
    hQval
  trans ∫ u : ℝ³, ((fderiv ℝ ψ x (kcStdBasis k)) * chiScale ℓ (x - ℓ • u)
      + (ψ x) * fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) ^ 2
  · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  · rw [hmain]
    ring

end Work.BSKinetic
