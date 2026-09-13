/-
# The mean value property of the limiting linear equation

The uniform limit `w` of classical solutions of `Fop (cofOp N) ε_k (D²·) = 0` (with `ε_k → 0`) is
a viscosity solution of the limiting constant-coefficient linear equation
`tr (cofOp N ∘ D²·) = 0`.  Substituting `B`, a symmetric square root of `cofOp N`, turns it into
the Laplacian equation for `y ↦ w (B y)` (`Submission.Savin.Spec` +
`Submission.Savin.ViscLinear`), so that function has the ball mean value property
(`Submission.ViscosityMVP.viscSubharmonic_ball_le` applied to it and to its negative).

NOTE the sign convention: since `M ↦ tr (cofOp N ∘ M)` is *increasing*, the proper (degenerate
elliptic) operator for the viscosity formulation is `M ↦ -tr (cofOp N ∘ M)`, and a classical
solution of `tr (cofOp N ∘ D²w) = 0` is a viscosity solution of `-tr (cofOp N ∘ D²·) = 0`.
This is the hypothesis `hvisc` below.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Spec
import Submission.Savin.ViscLinear
import Submission.ViscosityMVP
import Submission.Commons.Analysis.Harmonic.laplacian_nonneg_of_le_setAverage_ball

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- `negTrace (-S) = -negTrace S`. -/
theorem negTrace_neg (S : ℝ⁴ →L[ℝ] ℝ⁴) : negTrace (-S) = -negTrace S := by
  unfold negTrace
  rw [show ((-S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
      = -((S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl, map_neg]

/-- **Mean value property of the limit.**  If `w` is a continuous viscosity solution of
`-tr (cofOp N ∘ D²·) = 0` on an open set `s`, then there is a symmetric invertible square root `B`
of `cofOp N` such that `y ↦ w (B y)` has the ball mean value property on `B ⁻¹' s`. -/
theorem mvp_of_visc_linear {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp N v, v⟫)
    {w : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hwcont : ContinuousOn w s)
    (hvisc : IsViscSolution (fun M => -trOp (cofOp N * M)) w s) :
    ∃ B : ℝ⁴ →L[ℝ] ℝ⁴, B.IsSymmetric ∧ B * B = cofOp N ∧ B.IsInvertible ∧
      ∀ x ∈ B ⁻¹' s, ∀ r : ℝ, 0 < r → closedBall x r ⊆ B ⁻¹' s →
        w (B x) = ⨍ y in ball x r, w (B y) := by
  obtain ⟨B, hBsym, hBB⟩ := exists_sqrt_cofOp hN (fun v => le_trans (by positivity) (hcq v))
  have hpos : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪(B * B) v, v⟫ := by intro v; rw [hBB]; exact hcq v
  have hBinv : B.IsInvertible := isInvertible_of_sq_posdef hc hpos
  have hBinvsym : B.inverse.IsSymmetric := inverse_isSymmetric hBsym hBinv
  have hBBi : B * B.inverse = 1 := hBinv.self_comp_inverse
  have hBiB : B.inverse * B = 1 := hBinv.inverse_comp_self
  have hCeq : B.inverse * cofOp N * B.inverse = 1 := by
    rw [← hBB]
    have hassoc : B.inverse * (B * B) * B.inverse = (B.inverse * B) * (B * B.inverse) := by
      noncomm_ring
    rw [hassoc, hBiB, hBBi, one_mul]
  have hop2 : (fun M : ℝ⁴ →L[ℝ] ℝ⁴ =>
      -trOp ((B.inverse * cofOp N * B.inverse) * M)) = negTrace := by
    funext M
    have h1 : (B.inverse * cofOp N * B.inverse) * M = M := by
      rw [hCeq]
      exact one_mul M
    rw [h1]
    rfl
  have hsub : IsViscSubsolution negTrace (fun y => w (B y)) (B ⁻¹' s) := by
    have h0 := isViscSubsolution_comp_linear_neg hBBi hBiB hBinvsym (C := cofOp N) hs hvisc.1
    rwa [hop2] at h0
  have hsup : IsViscSupersolution negTrace (fun y => w (B y)) (B ⁻¹' s) := by
    have h0 := isViscSupersolution_comp_linear_neg hBBi hBiB hBinvsym (C := cofOp N) hs hvisc.2
    rwa [hop2] at h0
  have hs' : IsOpen (B ⁻¹' s) := hs.preimage B.continuous
  have hvcont : ContinuousOn (fun y => w (B y)) (B ⁻¹' s) :=
    hwcont.comp B.continuous.continuousOn (fun y hy => hy)
  have hsubvneg : IsViscSubsolution negTrace (fun y => -(w (B y))) (B ⁻¹' s) := by
    have h0 := (isViscSupersolution_iff hs').mp hsup
    have hop3 : (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => -negTrace (-M)) = negTrace := by
      funext M
      rw [negTrace_neg, neg_neg]
    rwa [hop3] at h0
  refine ⟨B, hBsym, hBB, hBinv, fun x hx r hr hclosed => ?_⟩
  have h1 := viscSubharmonic_ball_le hs' hvcont hsub hr hclosed
  have h2 := viscSubharmonic_ball_le hs' hvcont.neg hsubvneg hr hclosed
  have h3 : (⨍ y in ball x r, -(w (B y))) = -(⨍ y in ball x r, w (B y)) := by
    rw [show (fun y => -(w (B y))) = fun y => (-1 : ℝ) * w (B y) from by funext y; ring,
      Commons.Analysis.Harmonic.setAverage_mul_const_real]
    ring
  have h2' : -(w (B x)) ≤ ⨍ y in ball x r, -(w (B y)) := h2
  rw [h3] at h2'
  linarith [h1, h2']

end

end Submission
