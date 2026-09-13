/-
# The interior gradient estimate for smooth solutions of `sigma_2(D^2 u) = 1`, `Delta u > 0` in
dimension four

This file proves (Trudinger's interior gradient bound, as used in Shankar--Yuan `[TW]` Cor 3.4 /
Theorem 3.3): for a smooth solution of `sigma_2(D^2u) = 1` with `Delta u > 0` on the ball `B_r(0)`
one has
  `|Du(0)| <= C (1 + sup_{B_r} |u|)^2 / r`
with a universal constant `C`.

The proof is the classical maximum principle computation with the auxiliary function
`G(x) = |Du(x)| * exp (delta * (u x + C_0)^2) * (r^2 - |x|^2)`:
at an interior maximum `x_0` of `G` one has `D^2 (log G)(x_0) <= 0`, and contracting with the
positive definite matrix `F = sigma_1 * I - D^2u(x_0)` (the linearisation of `sigma_2`) and using
the twice differentiated equation gives the bound.

The main work is therefore
* the calculus: the diagonal second derivatives of `log G` in an eigenbasis of `D^2u(x_0)`,
* the first order conditions `D(log G)(x_0) = 0`,
* the linear algebra: `F >= 0`, `tr F = 3 sigma_1`, `tr (F A) = 2`, `F d d <= (3/2) sigma_1 |d|^2`,
  and the "ellipticity" bound `F d d >= (tr F / 3) |d|^2` whenever `A d d <= 0`.
-/
import Mathlib
import Submission.Prop21
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_grad_sq_diag
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_grad_sq_directional
import Submission.Commons.Analysis.Calculus.FDeriv.second_fderiv_log_laplacian_diag
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_const_mul
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
import Submission.Commons.Analysis.Calculus.FDeriv.first_deriv_sigma2_coord
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.Sigma2.linearized_upper_four
import Submission.Commons.Analysis.Sigma2.sum_linearized_mul_self
import Submission.Commons.Analysis.Sigma2.trace_sq_eq_two_add_trace_comp
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply
import Submission.Commons.Analysis.InnerProductSpace.norm_sq_eq_sum_sq_apply

open HessianEstimates
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-! ## The auxiliary function -/

/-- The weight `t ↦ exp (delta * (t + C_0)^2)`; its logarithm is the polynomial
`delta * (t + C_0)^2`. -/
noncomputable def hfun (δ C₀ t : ℝ) : ℝ := Real.exp (δ * (t + C₀) ^ 2)

theorem log_hfun (δ C₀ t : ℝ) : Real.log (hfun δ C₀ t) = δ * (t + C₀) ^ 2 :=
  Real.log_exp _

theorem hfun_pos (δ C₀ t : ℝ) : 0 < hfun δ C₀ t := Real.exp_pos _

/-- The auxiliary function of the maximum principle for the interior gradient estimate,
`G(z) = |Du(z)| * exp (delta (u z + C_0)^2) * (r^2 - |z|^2)`. -/
noncomputable def auxFun (u : ℝ⁴ → ℝ) (r δ C₀ : ℝ) : ℝ⁴ → ℝ :=
  fun z => ‖fderiv ℝ u z‖ * hfun δ C₀ (u z) * (r ^ 2 - ‖z‖ ^ 2)

theorem continuousOn_auxFun {u : ℝ⁴ → ℝ} {r δ C₀ : ℝ}
    (hc : ContinuousOn (fderiv ℝ u) (closedBall 0 r))
    (hu : ContinuousOn u (closedBall 0 r)) :
    ContinuousOn (auxFun u r δ C₀) (closedBall 0 r) := by
  have h1 : ContinuousOn (fun z : ℝ⁴ => ‖fderiv ℝ u z‖) (closedBall 0 r) := hc.norm
  have h2 : ContinuousOn (fun z : ℝ⁴ => hfun δ C₀ (u z)) (closedBall 0 r) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
      ((hu.add continuousOn_const).pow 2))
  have h3 : ContinuousOn (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) (closedBall 0 r) :=
    continuousOn_const.sub (continuous_norm.continuousOn.pow 2)
  exact (h1.mul h2).mul h3

theorem exists_max_auxFun {u : ℝ⁴ → ℝ} {r δ C₀ : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn (auxFun u r δ C₀) (closedBall 0 r)) :
    ∃ x₀ ∈ closedBall 0 r, ∀ z ∈ closedBall 0 r,
      auxFun u r δ C₀ z ≤ auxFun u r δ C₀ x₀ :=
  (isCompact_closedBall (0 : ℝ⁴) r).exists_isMaxOn (nonempty_closedBall.mpr hr.le) hcont


/-! ## Elementary derivative computations -/

open scoped RealInnerProductSpace in
theorem iteratedFDeriv_two_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x) (a b : E) :
    (iteratedFDeriv ℝ 2 (fun z => (w z) ^ 2) x) ![a, b]
      = 2 * (iteratedFDeriv ℝ 2 w x) ![a, b] * w x
        + 2 * (fderiv ℝ w x a) * (fderiv ℝ w x b) := by
  have hA : ∀ᶠ y in 𝓝 x, HasFDerivAt (fun z => (w z) ^ 2)
      ((2 * w y) • fderiv ℝ w y) y := by
    filter_upwards [hw.eventually (by norm_num)] with y hy
    have hd : DifferentiableAt ℝ w y := hy.differentiableAt (by norm_num)
    have h := hd.hasFDerivAt.pow 2
    simpa using h
  have hfe : fderiv ℝ (fun z => (w z) ^ 2) =ᶠ[𝓝 x] fun y => (2 * w y) • fderiv ℝ w y :=
    hA.mono fun y hy => hy.fderiv
  have hc : HasFDerivAt (fun y : E => 2 * w y) ((2 : ℝ) • fderiv ℝ w x) x :=
    (hw.differentiableAt (by norm_num)).hasFDerivAt.const_mul 2
  have hf : HasFDerivAt (fun y : E => fderiv ℝ w y) (fderiv ℝ (fderiv ℝ w) x) x :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hsm := hc.smul hf
  have hder : fderiv ℝ (fun y : E => (2 * w y) • fderiv ℝ w y) x
      = ((2 * w x) • fderiv ℝ (fderiv ℝ w) x)
        + ((2 : ℝ) • fderiv ℝ w x).smulRight (fderiv ℝ w x) := hsm.fderiv
  rw [iteratedFDeriv_two_apply, hfe.fderiv_eq, hder]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

open scoped RealInnerProductSpace in
theorem fderiv_zeta (r : ℝ) (x a : ℝ⁴) :
    fderiv ℝ (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) x a = -2 * ⟪x, a⟫ := by
  have h : HasFDerivAt (fun z : ℝ⁴ => ‖z‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [(h.const_sub (r ^ 2)).fderiv]
  simp [smul_apply, innerSL_apply_apply, smul_eq_mul]

theorem iteratedFDeriv_two_zeta (r : ℝ) (x a b : ℝ⁴) :
    (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) x) ![a, b] = -2 * ⟪a, b⟫ := by
  rw [iteratedFDeriv_two_apply]
  have hev : fderiv ℝ (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2)
      =ᶠ[𝓝 x] fun y : ℝ⁴ => (-(2 : ℝ)) • innerSL ℝ y := by
    filter_upwards with y
    have h : HasFDerivAt (fun z : ℝ⁴ => ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
      (hasStrictFDerivAt_norm_sq y).hasFDerivAt
    rw [(h.const_sub (r ^ 2)).fderiv]
    ext v
    simp only [smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  rw [hev.fderiv_eq]
  have h0 : HasFDerivAt (fun y : ℝ⁴ => (-(2 : ℝ)) • innerSL ℝ y)
      ((-(2 : ℝ)) • (innerSL ℝ : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ)) x := by
    have hh : HasFDerivAt (fun y : ℝ⁴ => (-(2 : ℝ)) • innerSL ℝ y)
        ((-(2 : ℝ)) • (innerSL ℝ : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ)) x :=
      (ContinuousLinearMap.hasFDerivAt (innerSL ℝ : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ)
        (x := x)).const_smul (-(2 : ℝ))
    exact hh
  rw [h0.fderiv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply]

open scoped RealInnerProductSpace in
theorem fderiv_log_zeta (r : ℝ) {x : ℝ⁴} (hx : r ^ 2 - ‖x‖ ^ 2 ≠ 0) (a : ℝ⁴) :
    fderiv ℝ (fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2)) x a
      = (-2 * ⟪x, a⟫) / (r ^ 2 - ‖x‖ ^ 2) := by
  have h : HasFDerivAt (fun z : ℝ⁴ => ‖z‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 : HasFDerivAt (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) (-(2 • innerSL ℝ x)) x :=
    h.const_sub (r ^ 2)
  rw [(h2.log hx).fderiv]
  simp only [smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul]
  ring

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem iteratedFDeriv_two_log_zeta_diag (r : ℝ) {x a : ℝ⁴} (hx : r ^ 2 - ‖x‖ ^ 2 ≠ 0)
    (ha : ⟪a, a⟫ = 1) :
    (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2)) x) ![a, a]
      = -2 / (r ^ 2 - ‖x‖ ^ 2) - 4 * (⟪x, a⟫) ^ 2 / (r ^ 2 - ‖x‖ ^ 2) ^ 2 := by
  have hcon : ContDiffAt ℝ 2 (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) x :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt)
  rw [Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_log_comp
    (g := fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) hcon hx a a]
  rw [iteratedFDeriv_two_zeta, fderiv_zeta, ha]
  field_simp
  ring

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- The function whose maximum is studied. -/
noncomputable def logAux (u : ℝ⁴ → ℝ) (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (r δ C₀ : ℝ) :
    ℝ⁴ → ℝ :=
  ((fun z => (1 / 2) * Real.log (∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2))
    + fun z => δ * (u z + C₀) ^ 2) + fun z => Real.log (r ^ 2 - ‖z‖ ^ 2)


open scoped RealInnerProductSpace in
theorem fderiv_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E → ℝ} {x : E}
    (hw : DifferentiableAt ℝ w x) (a : E) :
    fderiv ℝ (fun z => (w z) ^ 2) x a = 2 * w x * (fderiv ℝ w x a) := by
  have h : HasFDerivAt (fun z => (w z) ^ 2) ((2 * w x) • fderiv ℝ w x) x := by
    have hh := hw.hasFDerivAt.pow 2
    simpa using hh
  rw [h.fderiv]
  simp [smul_apply, smul_eq_mul]

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- First derivative of `logAux`. -/
theorem fderiv_logAux {u : ℝ⁴ → ℝ} {r δ C₀ : ℝ} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴}
    {s : Set ℝ⁴} {x w : ℝ⁴} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s)
    (hq : (∑ k : Fin 4, ((fderiv ℝ u x) (v k)) ^ 2) ≠ 0)
    (hζ : r ^ 2 - ‖x‖ ^ 2 ≠ 0) :
    fderiv ℝ (logAux u v r δ C₀) x w
      = (∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 2 u x) ![w, v k])
          / (∑ k : Fin 4, ((fderiv ℝ u x) (v k)) ^ 2)
        + 2 * δ * (u x + C₀) * (fderiv ℝ u x w)
        + (-2 * ⟪x, w⟫) / (r ^ 2 - ‖x‖ ^ 2) := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have hcat : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  have h2 : ContDiffAt ℝ 2 u x := hcat.of_le (by norm_num)
  have h1 : ContDiffAt ℝ 1 u x := hcat.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  set q : ℝ⁴ → ℝ := fun z => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2 with hqdef
  have hqsm : ContDiffAt ℝ 2 q x := by
    rw [hqdef]
    have hfdu : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y) x :=
      hcat.fderiv_right (m := 2) (by norm_num)
    have hAcd : ∀ k : Fin 4, ContDiffAt ℝ 2 (fun y : ℝ⁴ => (fderiv ℝ u y) (v k)) x :=
      fun k => ((ContinuousLinearMap.apply ℝ ℝ (v k)).contDiff.comp_contDiffAt x hfdu)
    exact ContDiffAt.sum (s := Finset.univ) (fun k _ => (hAcd k).pow 2)
  have hqne : q x ≠ 0 := by rw [hqdef]; exact hq
  have hA : HasFDerivAt (fun z => (1 / 2) * Real.log (q z))
      ((1 / 2 : ℝ) • ((q x)⁻¹ • fderiv ℝ q x)) x :=
    ((hqsm.differentiableAt (by norm_num)).hasFDerivAt.log hqne).const_mul (1 / 2)
  have hgdiff : DifferentiableAt ℝ (fun z : ℝ⁴ => u z + C₀) x :=
    (h1.differentiableAt (by norm_num)).add_const C₀
  have hB0 : HasFDerivAt (fun z : ℝ⁴ => (u z + C₀) ^ 2)
      ((2 * u x + 2 * C₀) • fderiv ℝ u x) x := by
    have hh := hgdiff.hasFDerivAt.pow 2
    simpa using hh
  have hB : HasFDerivAt (fun z => δ * (u z + C₀) ^ 2)
      (δ • ((2 * u x + 2 * C₀) • fderiv ℝ u x)) x :=
    hB0.const_mul δ
  have hζsm : ContDiffAt ℝ 2 (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) x :=
    contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
  have hC : HasFDerivAt (fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2))
      (((r ^ 2 - ‖x‖ ^ 2)⁻¹) • fderiv ℝ (fun z : ℝ⁴ => r ^ 2 - ‖z‖ ^ 2) x) x :=
    (hζsm.differentiableAt (by norm_num)).hasFDerivAt.log hζ
  have hsum := (hA.add hB).add hC
  have hfun : logAux u v r δ C₀ = ((fun z => (1 / 2) * Real.log (q z))
      + fun z => δ * (u z + C₀) ^ 2) + fun z => Real.log (r ^ 2 - ‖z‖ ^ 2) := by
    funext z
    simp only [logAux, Pi.add_apply, hqdef]
  rw [hfun, hsum.fderiv]
  rw [hqdef]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.add_apply]
  rw [Commons.Analysis.Calculus.FDeriv.fderiv_grad_sq_directional v hs hx hu2 w]
  rw [fderiv_zeta]
  field_simp

open scoped RealInnerProductSpace in
theorem iteratedFDeriv_two_add_lambda {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x a b : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (iteratedFDeriv ℝ 2 (fun z => f z + g z) x) ![a, b]
      = (iteratedFDeriv ℝ 2 f x) ![a, b] + (iteratedFDeriv ℝ 2 g x) ![a, b] := by
  rw [show (fun z : E => f z + g z) = f + g from by funext z; rfl]
  exact Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add hf hg

open scoped RealInnerProductSpace in
theorem iteratedFDeriv_two_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (c : ℝ) (a b : E) :
    (iteratedFDeriv ℝ 2 (fun z => u z + c) x) ![a, b] = (iteratedFDeriv ℝ 2 u x) ![a, b] := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  congr 1
  have hev : fderiv ℝ (fun z : E => u z + c) =ᶠ[𝓝 x] fderiv ℝ u :=
    Filter.Eventually.of_forall fun y => fderiv_add_const c
  rw [hev.fderiv_eq]

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- **The diagonal second derivative of `logAux`** in an orthonormal basis: this is the heart of
the maximum principle computation. -/
theorem iteratedFDeriv_two_logAux_diag {u : ℝ⁴ → ℝ} {r δ C₀ : ℝ}
    {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {s : Set ℝ⁴} {x : ℝ⁴}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s)
    (hq : (∑ k : Fin 4, ((fderiv ℝ u x) (v k)) ^ 2) ≠ 0)
    (hζ : r ^ 2 - ‖x‖ ^ 2 ≠ 0) (i : Fin 4) :
    (iteratedFDeriv ℝ 2 (logAux u v r δ C₀) x) ![v i, v i]
      = ((∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2)
          + (∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]))
          / (∑ k : Fin 4, ((fderiv ℝ u x) (v k)) ^ 2)
        - 2 * (∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 2 u x) ![v i, v k]) ^ 2
          / (∑ k : Fin 4, ((fderiv ℝ u x) (v k)) ^ 2) ^ 2
        + 2 * δ * (u x + C₀) * (iteratedFDeriv ℝ 2 u x) ![v i, v i]
        + 2 * δ * ((fderiv ℝ u x) (v i)) ^ 2
        - 2 / (r ^ 2 - ‖x‖ ^ 2)
        - 4 * (⟪x, v i⟫) ^ 2 / (r ^ 2 - ‖x‖ ^ 2) ^ 2 := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have hcat : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  have h2 : ContDiffAt ℝ 2 u x := hcat.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  have hii : ⟪v i, v i⟫ = (1 : ℝ) := by
    rw [orthonormal_iff_ite.mp v.orthonormal i i]; simp
  set q : ℝ⁴ → ℝ := fun z => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2 with hqdef
  have hqsm : ContDiffAt ℝ 2 q x := by
    rw [hqdef]
    have hfdu : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y) x :=
      hcat.fderiv_right (m := 2) (by norm_num)
    have hAcd : ∀ k : Fin 4, ContDiffAt ℝ 2 (fun y : ℝ⁴ => (fderiv ℝ u y) (v k)) x :=
      fun k => ((ContinuousLinearMap.apply ℝ ℝ (v k)).contDiff.comp_contDiffAt x hfdu)
    exact ContDiffAt.sum (s := Finset.univ) (fun k _ => (hAcd k).pow 2)
  have hqne : q x ≠ 0 := by rw [hqdef]; exact hq
  have hdq : fderiv ℝ q x (v i)
      = 2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 2 u x) ![v i, v k] := by
    rw [hqdef]
    exact Commons.Analysis.Calculus.FDeriv.fderiv_grad_sq_directional v hs hx hu2 (v i)
  have hd2q : (iteratedFDeriv ℝ 2 q x) ![v i, v i]
      = 2 * (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2)
        + 2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
    rw [hqdef]
    exact Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_grad_sq_diag v hs hx hu i
  have hlogsm : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log (q z)) x := hqsm.log hqne
  have hlogq : (iteratedFDeriv ℝ 2 (fun z => Real.log (q z)) x) ![v i, v i]
      = (iteratedFDeriv ℝ 2 q x) ![v i, v i] / q x - (fderiv ℝ q x (v i)) ^ 2 / (q x) ^ 2 := by
    rw [Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_log_comp hqsm hqne (v i) (v i)]
    ring
  have hf1 : (iteratedFDeriv ℝ 2 (fun z => (1 / 2) * Real.log (q z)) x) ![v i, v i]
      = (1 / 2) * ((iteratedFDeriv ℝ 2 q x) ![v i, v i] / q x
          - (fderiv ℝ q x (v i)) ^ 2 / (q x) ^ 2) := by
    rw [Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_const_mul (1 / 2)
      (hlogsm.differentiableAt (by norm_num))
      ((hlogsm.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)), hlogq]
  have hsm1 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (1 / 2) * Real.log (q z)) x :=
    contDiffAt_const.mul hlogsm
  have hwsm : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (u z + C₀) ^ 2) x :=
    (h2.add contDiffAt_const).pow 2
  have hf2 : (iteratedFDeriv ℝ 2 (fun z => δ * (u z + C₀) ^ 2) x) ![v i, v i]
      = δ * (2 * (u x + C₀) * (iteratedFDeriv ℝ 2 u x) ![v i, v i]
        + 2 * (fderiv ℝ u x (v i)) ^ 2) := by
    rw [Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_const_mul δ
      (hwsm.differentiableAt (by norm_num))
      ((hwsm.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
    congr 1
    rw [iteratedFDeriv_two_sq ((h2.add contDiffAt_const)) (v i) (v i),
      iteratedFDeriv_two_add_const h2 C₀ (v i) (v i), fderiv_add_const]
    ring
  have hsm2 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => δ * (u z + C₀) ^ 2) x :=
    contDiffAt_const.mul hwsm
  have hsm3 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2)) x :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).log hζ
  have haux3 : (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2)) x) ![v i, v i]
      = -2 / (r ^ 2 - ‖x‖ ^ 2) - 4 * (⟪x, v i⟫) ^ 2 / (r ^ 2 - ‖x‖ ^ 2) ^ 2 :=
    iteratedFDeriv_two_log_zeta_diag r hζ hii
  have h12 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (1 / 2) * Real.log (q z) + δ * (u z + C₀) ^ 2) x :=
    hsm1.add hsm2
  have hLfun : logAux u v r δ C₀ = fun z => ((1 / 2) * Real.log (q z) + δ * (u z + C₀) ^ 2)
      + Real.log (r ^ 2 - ‖z‖ ^ 2) := by
    funext z
    simp only [logAux, Pi.add_apply, hqdef]
  rw [hLfun]
  rw [iteratedFDeriv_two_add_lambda (f := fun z : ℝ⁴ => (1 / 2) * Real.log (q z)
        + δ * (u z + C₀) ^ 2) (g := fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2)) h12 hsm3]
  rw [iteratedFDeriv_two_add_lambda (f := fun z : ℝ⁴ => (1 / 2) * Real.log (q z))
    (g := fun z : ℝ⁴ => δ * (u z + C₀) ^ 2) hsm1 hsm2]
  rw [hf1, hf2, haux3]
  rw [hd2q, hdq]
  simp only [hqdef]
  field_simp
  ring

end Submission