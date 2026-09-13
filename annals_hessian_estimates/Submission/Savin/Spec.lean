/-
# The Hessian of a linear substitution and the limiting linear operator

For a symmetric `B` the substitution `w ↦ w ∘ B` turns the Hessian into
`B ∘ D²w ∘ B` (`hessOp_comp_linear`), so the trace becomes
`Δ (w ∘ B) = tr ((B * B) ∘ D²w) ∘ B`.

Taking `B` a symmetric square root of `cofOp N` (whose existence is
`Commons.LinearAlgebra.InnerProductSpace.exists_isSymmetric_mul_self` applied to the positive
definite operator `cofOp N`), the limiting equation `tr (cofOp N ∘ D²w) = 0` of Savin's
Proposition 4.1 becomes the Laplacian equation `Δ (w ∘ B) = 0`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Linear
import Submission.Savin.HarnackIneq
import Submission.Commons.Analysis.Harmonic.laplacian_nonneg_of_le_setAverage_ball
import Submission.Commons.LinearAlgebra.InnerProductSpace.exists_isSymmetric_mul_self

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The trace of a product is symmetric in the two factors. -/
theorem trOp_mul_comm (S T : ℝ⁴ →L[ℝ] ℝ⁴) : trOp (S * T) = trOp (T * S) := by
  have h := LinearMap.trace_comp_comm' (R := ℝ) (S : ℝ⁴ →ₗ[ℝ] ℝ⁴) (T : ℝ⁴ →ₗ[ℝ] ℝ⁴)
  unfold trOp
  rw [show ((S * T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
        = (S : ℝ⁴ →ₗ[ℝ] ℝ⁴) ∘ₗ (T : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl,
    show ((T * S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
        = (T : ℝ⁴ →ₗ[ℝ] ℝ⁴) ∘ₗ (S : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl]
  exact h.symm

/-- `tr (-S) = -tr S`. -/
theorem trOp_neg (S : ℝ⁴ →L[ℝ] ℝ⁴) : trOp (-S) = -trOp S := by
  unfold trOp
  rw [show ((-S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
      = -((S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl, map_neg]

/-- `tr ((B M) B) = tr ((B B) M)`. -/
theorem trOp_conj (B M : ℝ⁴ →L[ℝ] ℝ⁴) : trOp ((B * M) * B) = trOp ((B * B) * M) := by
  rw [trOp_mul_comm (B * M) B, ← mul_assoc]

/-- The Laplacian of a `C²` function is the trace of its Hessian operator. -/
theorem laplacian_eq_trOp_hessOp {φ : ℝ⁴ → ℝ} {x : ℝ⁴} (hφ : ContDiffAt ℝ 2 φ x) :
    Laplacian.laplacian φ x = trOp (hessOp φ x) := by
  rw [Commons.Analysis.Harmonic.laplacian_eq_sum_fderiv_fderiv, trOp_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [stdB4_apply, hessOp, InnerProductSpace.continuousLinearMapOfBilin_apply]

/-- **The Laplacian of a linear substitution.**  For a symmetric `B` (and `w` `C²` at `B x`),

  `Δ (fun y => w (B y)) x = tr ((B * B) * hessOp w (B x))`. -/
theorem laplacian_comp_linear {B : ℝ⁴ →L[ℝ] ℝ⁴} (hB : B.IsSymmetric) {w : ℝ⁴ → ℝ} {x : ℝ⁴}
    (hw : ContDiffAt ℝ 2 w (B x)) :
    Laplacian.laplacian (fun y => w (B y)) x = trOp ((B * B) * hessOp w (B x)) := by
  have hcont : ContDiffAt ℝ 2 (fun y : ℝ⁴ => w (B y)) x := hw.comp x B.contDiff.contDiffAt
  have hcomp : B.adjoint.comp ((hessOp w (B x)).comp B) = (B * (hessOp w (B x))) * B := by
    rw [hB.clm_adjoint_eq, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  rw [laplacian_eq_trOp_hessOp hcont, hessOp_comp_linear hw, hcomp, trOp_conj]

/-- **The limiting linear operator becomes the Laplacian.**  If `B` is a symmetric square root of
`cofOp N` (`B * B = cofOp N`) then along the substitution `w ↦ w ∘ B` the operator
`M ↦ tr (cofOp N ∘ M)` is the Laplacian: `Δ (w ∘ B) = tr (cofOp N ∘ hessOp w) ∘ B`. -/
theorem laplacian_comp_linear_cofOp {B N : ℝ⁴ →L[ℝ] ℝ⁴} (hB : B.IsSymmetric)
    (hBB : B * B = cofOp N) {w : ℝ⁴ → ℝ} {x : ℝ⁴} (hw : ContDiffAt ℝ 2 w (B x)) :
    Laplacian.laplacian (fun y => w (B y)) x = trOp (cofOp N * hessOp w (B x)) := by
  rw [laplacian_comp_linear hB hw, hBB]

/-- **A symmetric square root of `cofOp N`.** -/
theorem exists_sqrt_cofOp {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric)
    (hC : ∀ v : ℝ⁴, 0 ≤ ⟪cofOp N v, v⟫) :
    ∃ B : ℝ⁴ →L[ℝ] ℝ⁴, B.IsSymmetric ∧ B * B = cofOp N :=
  Commons.LinearAlgebra.InnerProductSpace.exists_isSymmetric_mul_self (cofOp_isSymmetric hN) hC

/-- A continuous linear map whose `B * B` is positive definite is invertible (finite
dimensionality: injectivity suffices). -/
theorem isInvertible_of_sq_posdef {B : ℝ⁴ →L[ℝ] ℝ⁴} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪(B * B) v, v⟫) : B.IsInvertible := by
  have hinj : Function.Injective (B : ℝ⁴ → ℝ⁴) := by
    intro v w hvw
    have hv : B (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h2 : (B * B) (v - w) = B (B (v - w)) := by
      show (B * B) (v - w) = B (B (v - w))
      rw [_root_.mul_apply_eq_comp]
    have h1 : ⟪(B * B) (v - w), (v - w)⟫ = 0 := by
      rw [h2, hv, map_zero, inner_zero_left]
    have h3 := hpos (v - w)
    have h4 : ‖v - w‖ ^ 2 = 0 := by nlinarith [h3, h1]
    have h5 : ‖v - w‖ = 0 := sq_eq_zero_iff.mp h4
    exact sub_eq_zero.mp (norm_eq_zero.mp h5)
  have hsurj : Function.Surjective (B : ℝ⁴ → ℝ⁴) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (rfl : Module.finrank ℝ ℝ⁴
      = Module.finrank ℝ ℝ⁴)).mp hinj
  refine ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective B _ _

/-- **The inverse of a symmetric invertible operator is symmetric.** -/
theorem inverse_isSymmetric {B : ℝ⁴ →L[ℝ] ℝ⁴} (hB : B.IsSymmetric) (hinv : B.IsInvertible) :
    B.inverse.IsSymmetric := by
  intro v w
  have h1 : B (B.inverse w) = w := hinv.self_apply_inverse w
  have h2 : B (B.inverse v) = v := hinv.self_apply_inverse v
  calc ⟪B.inverse v, w⟫ = ⟪B.inverse v, B (B.inverse w)⟫ := by rw [h1]
    _ = ⟪B (B.inverse v), B.inverse w⟫ := (hB (B.inverse v) (B.inverse w)).symm
    _ = ⟪v, B.inverse w⟫ := by rw [h2]

end

end Submission
