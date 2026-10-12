import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.UBBInputs9.B.integral_chiB_mul_partialDeriv_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.Basic` — the one-particle slot calculus for the sliding window

The target `B/integral_dirichlet_chiB_eq` differentiates, on `X 1 = Fin 1 → ℝ³`, the product
`y ↦ χ_{B(u)}(y 0) · Φ y` in the kinetic directions `kcDir 1 0 k`.  Since `X 1 ≃ ℝ³` through
the projection `y ↦ y 0`, every such derivative is a derivative of an `ℝ³`-function composed
with the projection.

This module packages the calculus:

* `projX1 : X 1 →L[ℝ] ℝ³` — the slot-`0` projection, `projX1 y = y 0`, with
  `projX1 (kcDir 1 0 k) = kcStdBasis k`;
* `fderiv_liftX_apply`, `fderiv_liftX_sub_const_apply` — the chain rule for
  `y ↦ f (y 0)` and `y ↦ f (y 0 - c)`;
* `fderiv_chiBPhi_eq` — the two-term Leibniz formula that splits the sliding window
  `χ_{B(u)}(x) = χ(x/ℓ)·χ(x/(ℓd) − u)` away from the state `Φ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The slot-`0` coordinate projection `X 1 → ℝ³`. -/
noncomputable def projX1 : X1 →L[ℝ] ℝ³ := ContinuousLinearMap.proj (0 : Fin 1)

lemma projX1_apply (y : X1) : projX1 y = y 0 := rfl

lemma projX1_kcDir (k : Fin 3) : projX1 (kcDir 1 0 k) = kcStdBasis k := by
  simp [projX1, kcDir, kcStdBasis]

lemma differentiableAt_projX1 (x : X1) : DifferentiableAt ℝ (fun y : X1 => y 0) x :=
  ContinuousLinearMap.differentiableAt projX1

lemma fderiv_projX1 (x : X1) : fderiv ℝ (fun y : X1 => y 0) x = projX1 :=
  ContinuousLinearMap.fderiv projX1

lemma hasFDerivAt_projX1 (x : X1) : HasFDerivAt (fun y : X1 => y 0) projX1 x :=
  ContinuousLinearMap.hasFDerivAt projX1

lemma hasFDerivAt_projX1_sub_const (c : ℝ³) (x : X1) :
    HasFDerivAt (fun y : X1 => y 0 - c) projX1 x := by
  simpa [sub_eq_add_neg] using (hasFDerivAt_projX1 x).sub_const c

/-- Chain rule for the lifted function `y ↦ f (y 0)`. -/
lemma fderiv_liftX (f : ℝ³ → ℝ) (x : X1) (hf : DifferentiableAt ℝ f (x 0)) :
    fderiv ℝ (fun y : X1 => f (y 0)) x = (fderiv ℝ f (x 0)).comp projX1 := by
  have hfun : (fun y : X1 => f (y 0)) = f ∘ projX1 := rfl
  rw [hfun, fderiv_comp x hf (ContinuousLinearMap.differentiableAt projX1),
    ContinuousLinearMap.fderiv]
  simp only [projX1_apply]

/-- Evaluated form of `fderiv_liftX`. -/
lemma fderiv_liftX_apply (f : ℝ³ → ℝ) (x : X1) (hf : DifferentiableAt ℝ f (x 0))
    (k : Fin 3) :
    fderiv ℝ (fun y : X1 => f (y 0)) x (kcDir 1 0 k) = fderiv ℝ f (x 0) (kcStdBasis k) := by
  rw [fderiv_liftX f x hf, ContinuousLinearMap.comp_apply, projX1_kcDir]

/-- Chain rule for the shifted lifted function `y ↦ f (y 0 - c)`. -/
lemma fderiv_liftX_sub_const (f : ℝ³ → ℝ) (c : ℝ³) (x : X1)
    (hf : DifferentiableAt ℝ f (x 0 - c)) :
    fderiv ℝ (fun y : X1 => f (y 0 - c)) x = (fderiv ℝ f (x 0 - c)).comp projX1 := by
  have hfun : (fun y : X1 => f (y 0 - c)) = f ∘ (fun y : X1 => y 0 - c) := rfl
  rw [hfun, fderiv_comp x hf (hasFDerivAt_projX1_sub_const c x).differentiableAt,
    (hasFDerivAt_projX1_sub_const c x).fderiv]

/-- Evaluated form of `fderiv_liftX_sub_const`. -/
lemma fderiv_liftX_sub_const_apply (f : ℝ³ → ℝ) (c : ℝ³) (x : X1)
    (hf : DifferentiableAt ℝ f (x 0 - c)) (k : Fin 3) :
    fderiv ℝ (fun y : X1 => f (y 0 - c)) x (kcDir 1 0 k)
      = fderiv ℝ f (x 0 - c) (kcStdBasis k) := by
  rw [fderiv_liftX_sub_const f c x hf, ContinuousLinearMap.comp_apply, projX1_kcDir]

/-- **The Leibniz formula for the sliding window.**  Splitting
`χ_{B(u)}(y 0) = χ(y 0/ℓ)·χ(y 0/(ℓd) − u)` off the state `Φ`, the derivative of the product
along `kcDir 1 0 k` is

    ∂_k (χ_{B(u)}·Φ)(x)
      = ∂_k (χ(x/ℓ)·Φ)(x) · χ(x/(ℓd) − u) + χ(x/ℓ) Φ(x) · (∂_k χ)(x/(ℓd) − u).

Both `χ(x/ℓ) = chiScale ℓ (x 0)` and `χ(x/(ℓd) − u) = chiScale (ℓd) (x 0 − (ℓd)•u)`. -/
lemma fderiv_chiBPhi_eq (ℓ d : ℝ) {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (u : ℝ³) (x : X1) (k : Fin 3) :
    fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0) * Φ y) x (kcDir 1 0 k)
      = (fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
          * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
        + (chiScale ℓ (x 0) * Φ x)
          * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)) := by
  set G : X1 → ℝ := fun y => chiScale ℓ (y 0) * Φ y with hG
  set H : X1 → ℝ := fun y => chiScale (ℓ * d) (y 0 - (ℓ * d) • u) with hH
  have hchiScale_diff : ∀ a : ℝ, Differentiable ℝ (chiScale a) := fun a =>
    (ChiDeriv.chiScale_contDiff_any a).differentiable (by norm_num)
  have hGdiff : DifferentiableAt ℝ G x := by
    rw [hG]
    exact ((hchiScale_diff ℓ).differentiableAt.comp x (differentiableAt_projX1 x)).mul
      (hΦ.differentiable (by norm_num) x)
  have hHdiff : DifferentiableAt ℝ H x := by
    rw [hH]
    exact (hchiScale_diff (ℓ * d)).differentiableAt.comp x
      ((differentiableAt_projX1 x).sub_const _)
  have hfun : (fun y : X1 => chiB ℓ d u (y 0) * Φ y) = G * H := by
    funext y
    rw [hG, hH]
    simp only [Pi.mul_apply]
    rw [chiB]
    ring
  rw [hfun, fderiv_mul hGdiff hHdiff, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_liftX_sub_const_apply (chiScale (ℓ * d)) ((ℓ * d) • u) x
      ((hchiScale_diff (ℓ * d)).differentiableAt) k,
    show fderiv ℝ G x (kcDir 1 0 k)
        = fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k) from rfl,
    show H x = chiScale (ℓ * d) (x 0 - (ℓ * d) • u) from rfl,
    show G x = chiScale ℓ (x 0) * Φ x from rfl]
  ring

end Work.UBBInputs9.B
