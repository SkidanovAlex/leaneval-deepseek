/-
# The interior gradient estimate for smooth solutions of `sigma_2(D^2 u) = 1`, `Delta u > 0`
(dimension four): the maximum-principle assembly.

This file continues `Submission/SmoothGradient.lean`.  It contains the bridge
`exp (logAux) = auxFun`, the transfer of the maximum principle to `logAux`, and the main
theorem `interior_gradient_bound`:

  `|Du(0)| * r ≤ C (1 + M)^2`  for a smooth solution on `B_r(0)` with `|u| ≤ M` there.
-/
import Mathlib
import Submission.SmoothGradient
import Submission.Commons.Analysis.Calculus.Bounds.gradient_arith
import Submission.Commons.Algebra.BigOperators.sum_logAux_bound
import Submission.Commons.Algebra.BigOperators.sum_sq_mul_eq_of_mul_eq
import Submission.Commons.Analysis.InnerProductSpace.weighted_cauchy_schwarz
import Submission.Commons.Analysis.Sigma2.cofactor_psd_four
import Submission.Commons.Analysis.Sigma2.cofactor_quad_le_three_halves
import Submission.Commons.Analysis.Sigma2.cofactor_third_diag_sum_zero
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_eigen
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.Sigma2.linearized_upper_four
import Submission.Commons.Analysis.Sigma2.sum_linearized_mul_self
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv

open HessianEstimates
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- Where the two factors are positive, `exp (logAux) = auxFun`. -/
theorem exp_logAux_eq_auxFun {u : ℝ⁴ → ℝ} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {r δ C₀ : ℝ}
    {z : ℝ⁴} (hq : 0 < ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2)
    (hζ : 0 < r ^ 2 - ‖z‖ ^ 2) :
    Real.exp (logAux u v r δ C₀ z) = auxFun u r δ C₀ z := by
  have hS : (∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) = ‖fderiv ℝ u z‖ ^ 2 :=
    (Commons.Analysis.InnerProductSpace.norm_sq_eq_sum_sq_apply v (fderiv ℝ u z)).symm
  have hexp : Real.exp ((1 / 2) * Real.log (∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2))
      = ‖fderiv ℝ u z‖ := by
    have hsq : (0 : ℝ) < ‖fderiv ℝ u z‖ ^ 2 := by rw [← hS]; exact hq
    have hne : ‖fderiv ℝ u z‖ ≠ 0 := by intro h; rw [h] at hsq; simp at hsq
    have hpos : (0 : ℝ) < ‖fderiv ℝ u z‖ := lt_of_le_of_ne' (norm_nonneg _) hne
    rw [hS, mul_comm, ← Real.rpow_def_of_pos (pow_pos hpos 2),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  simp only [logAux, auxFun, Pi.add_apply, hfun]
  rw [Real.exp_add, Real.exp_add, hexp, Real.exp_log hζ]

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- Where the two factors are positive, `logAux = log ∘ auxFun`. -/
theorem logAux_eq_log_auxFun {u : ℝ⁴ → ℝ} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {r δ C₀ : ℝ}
    {z : ℝ⁴} (hq : 0 < ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2)
    (hζ : 0 < r ^ 2 - ‖z‖ ^ 2) :
    logAux u v r δ C₀ z = Real.log (auxFun u r δ C₀ z) := by
  rw [← exp_logAux_eq_auxFun (u := u) (v := v) (r := r) (δ := δ) (C₀ := C₀) hq hζ,
    Real.log_exp]

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- `logAux` is `C²` wherever `u` is `C³` and the two factors are nonzero. -/
theorem contDiffAt_logAux {u : ℝ⁴ → ℝ} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {r δ C₀ : ℝ}
    {s : Set ℝ⁴} {x : ℝ⁴} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s)
    (hq : (∑ k : Fin 4, ((fderiv ℝ u x) (v k)) ^ 2) ≠ 0)
    (hζ : r ^ 2 - ‖x‖ ^ 2 ≠ 0) :
    ContDiffAt ℝ 2 (logAux u v r δ C₀) x := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have hcat : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  set q : ℝ⁴ → ℝ := fun z => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2 with hqdef
  have hqsm : ContDiffAt ℝ 2 q x := by
    rw [hqdef]
    have hfdu : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y) x :=
      hcat.fderiv_right (m := 2) (by norm_num)
    have hAcd : ∀ k : Fin 4, ContDiffAt ℝ 2 (fun y : ℝ⁴ => (fderiv ℝ u y) (v k)) x :=
      fun k => ((ContinuousLinearMap.apply ℝ ℝ (v k)).contDiff.comp_contDiffAt x hfdu)
    exact ContDiffAt.sum (s := Finset.univ) (fun k _ => (hAcd k).pow 2)
  have hqne : q x ≠ 0 := by rw [hqdef]; exact hq
  have hlogsm : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log (q z)) x := hqsm.log hqne
  have hwsm : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (u z + C₀) ^ 2) x :=
    ((hcat.of_le (by norm_num)).add contDiffAt_const).pow 2
  have h12 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (1 / 2) * Real.log (q z) + δ * (u z + C₀) ^ 2) x :=
    (contDiffAt_const.mul hlogsm).add (contDiffAt_const.mul hwsm)
  have hsm3 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log (r ^ 2 - ‖z‖ ^ 2)) x :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).log hζ
  have hLfun : logAux u v r δ C₀
      = fun z => ((1 / 2) * Real.log (q z) + δ * (u z + C₀) ^ 2)
          + Real.log (r ^ 2 - ‖z‖ ^ 2) := by
    funext z
    simp only [logAux, Pi.add_apply, hqdef]
  rw [hLfun]
  exact h12.add hsm3

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- **The maximum-principle core of Trudinger's interior gradient estimate.**

`x₀` is a point of `closedBall 0 r` maximising the auxiliary function
`auxFun u r δ C₀ z = |Du(z)| * exp (δ (u z + C₀)^2) * (r^2 - |z|^2)`.  Then
`|Du(0)| r ≤ 512 (1 + M)^2`. -/
theorem gradient_bound_of_max {u : ℝ⁴ → ℝ} {r M δ C₀ : ℝ} {s : Set ℝ⁴}
    (hs : IsOpen s) (hball : closedBall (0 : ℝ⁴) r ⊆ s) (hr : 0 < r) (hM : 0 < M)
    (hC₀ : C₀ = M + 1) (hδ : δ = 1 / (64 * C₀ ^ 2))
    (hu3 : ContDiffOn ℝ 3 u s)
    (hub : ∀ x ∈ closedBall (0 : ℝ⁴) r, |u x| ≤ M)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1)
    (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {x₀ : ℝ⁴} (hx₀r : x₀ ∈ closedBall (0 : ℝ⁴) r)
    (hmax : ∀ z ∈ closedBall (0 : ℝ⁴) r, auxFun u r δ C₀ z ≤ auxFun u r δ C₀ x₀) :
    ‖fderiv ℝ u 0‖ * r ≤ 512 * (1 + M) ^ 2 := by
  have hC₀1 : 1 ≤ C₀ := by rw [hC₀]; linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀1
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have h0mem : (0 : ℝ⁴) ∈ closedBall (0 : ℝ⁴) r := by
    rw [Metric.mem_closedBall, dist_self]; exact hr.le
  have hmax0 : auxFun u r δ C₀ 0 ≤ auxFun u r δ C₀ x₀ := hmax 0 h0mem
  have haux0 : auxFun u r δ C₀ 0 = ‖fderiv ℝ u 0‖ * hfun δ C₀ (u 0) * r ^ 2 := by
    simp [auxFun]
  rcases le_or_gt (auxFun u r δ C₀ x₀) 0 with hle | hgt
  · have hlt : ‖fderiv ℝ u 0‖ * hfun δ C₀ (u 0) * r ^ 2 ≤ 0 := by
      rw [← haux0]; linarith
    have hz : ‖fderiv ℝ u 0‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖fderiv ℝ u 0‖ := lt_of_le_of_ne' (norm_nonneg _) hne
      have h1 : 0 < ‖fderiv ℝ u 0‖ * hfun δ C₀ (u 0) * r ^ 2 :=
        mul_pos (mul_pos hpos (hfun_pos δ C₀ (u 0))) (pow_pos hr 2)
      linarith
    rw [hz]
    simp only [zero_mul]
    positivity
  · have hubx : |u x₀| ≤ M := hub x₀ hx₀r
    have hub0 : |u 0| ≤ M := hub 0 h0mem
    have hζpos : 0 < r ^ 2 - ‖x₀‖ ^ 2 := by
      have h1 : 0 < ‖fderiv ℝ u x₀‖ * hfun δ C₀ (u x₀) * (r ^ 2 - ‖x₀‖ ^ 2) := by
        simpa only [auxFun] using hgt
      exact ((mul_pos_iff.mp h1).resolve_right
        (fun h => absurd h.1
          (not_lt_of_ge (mul_nonneg (norm_nonneg _) (hfun_pos δ C₀ (u x₀)).le)))).2
    have hDupos : 0 < ‖fderiv ℝ u x₀‖ := by
      have h1 : 0 < ‖fderiv ℝ u x₀‖ * hfun δ C₀ (u x₀) * (r ^ 2 - ‖x₀‖ ^ 2) := by
        simpa only [auxFun] using hgt
      have h2 := (mul_pos_iff.mp h1).resolve_right
        (fun h => absurd h.1
          (not_lt_of_ge (mul_nonneg (norm_nonneg _) (hfun_pos δ C₀ (u x₀)).le)))
      exact ((mul_pos_iff.mp h2.1).resolve_right
        (fun h => absurd h.2 (not_lt_of_ge (hfun_pos δ C₀ (u x₀)).le))).1
    have hx₀lt : ‖x₀‖ < r := by
      nlinarith [hζpos, norm_nonneg x₀, hr]
    have hx₀ball : x₀ ∈ ball (0 : ℝ⁴) r := by
      rw [Metric.mem_ball, dist_zero_right]; exact hx₀lt
    have hx₀s : x₀ ∈ s := hball (ball_subset_closedBall hx₀ball)
    obtain ⟨v, lam, hdiag, hmono⟩ := exists_diagonal_basis hs (hu3.of_le (by norm_num)) hx₀s
    have hqpos : 0 < ∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2 := by
      rw [← Commons.Analysis.InnerProductSpace.norm_sq_eq_sum_sq_apply v (fderiv ℝ u x₀)]
      exact pow_pos hDupos 2
    -- the local maximum of `logAux` at `x₀`
    have hUmem : ({z : ℝ⁴ | 0 < ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2} ∩ ball (0 : ℝ⁴) r)
        ∈ 𝓝 x₀ := by
      refine Filter.inter_mem ?_ (isOpen_ball.mem_nhds hx₀ball)
      have hcat : ContDiffAt ℝ 3 u x₀ := hu3.contDiffAt (hs.mem_nhds hx₀s)
      have hfdu : ContinuousAt (fun z : ℝ⁴ => fderiv ℝ u z) x₀ :=
        (hcat.fderiv_right (m := 2) (by norm_num)).continuousAt
      have hcont : ContinuousAt (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) x₀ := by
        have h1 : ∀ k : Fin 4, ContinuousAt (fun z : ℝ⁴ => ((fderiv ℝ u z) (v k)) ^ 2) x₀ :=
          fun k => ((((ContinuousLinearMap.apply ℝ ℝ (v k)).continuous.continuousAt).comp hfdu)).pow 2
        simp only [Fin.sum_univ_four]
        exact (((h1 0).add (h1 1)).add (h1 2)).add (h1 3)
      exact hcont.eventually (isOpen_Ioi.mem_nhds hqpos)
    have hmaxOn : IsLocalMaxOn (logAux u v r δ C₀)
        ({z : ℝ⁴ | 0 < ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2} ∩ ball (0 : ℝ⁴) r) x₀ := by
      filter_upwards [self_mem_nhdsWithin] with z hzU
      have hzq : 0 < ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2 := hzU.1
      have hzlt : ‖z‖ < r := by
        have := hzU.2
        rw [Metric.mem_ball, dist_zero_right] at this
        exact this
      have hzζ : 0 < r ^ 2 - ‖z‖ ^ 2 := by nlinarith [hzlt, norm_nonneg z, hr]
      have hzDupos : 0 < ‖fderiv ℝ u z‖ := by
        have h : 0 < ‖fderiv ℝ u z‖ ^ 2 := by
          rw [← Commons.Analysis.InnerProductSpace.norm_sq_eq_sum_sq_apply v (fderiv ℝ u z)] at hzq
          exact hzq
        exact lt_of_le_of_ne' (norm_nonneg _) (by intro h0; rw [h0] at h; simp at h)
      have hzauxpos : 0 < auxFun u r δ C₀ z := by
        rw [auxFun]
        exact mul_pos (mul_pos hzDupos (hfun_pos δ C₀ (u z))) hzζ
      rw [logAux_eq_log_auxFun (u := u) (v := v) (r := r) (δ := δ) (C₀ := C₀) hzq hzζ,
        logAux_eq_log_auxFun (u := u) (v := v) (r := r) (δ := δ) (C₀ := C₀) hqpos hζpos]
      refine Real.log_le_log hzauxpos ?_
      exact hmax z (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hzlt)
    have hmaxL : IsLocalMax (logAux u v r δ C₀) x₀ :=
      hmaxOn.isLocalMax hUmem
    have hcd : ContDiffAt ℝ 2 (logAux u v r δ C₀) x₀ :=
      contDiffAt_logAux hs hx₀s hu3 (ne_of_gt hqpos) (ne_of_gt hζpos)
    have hfderiv0 : fderiv ℝ (logAux u v r δ C₀) x₀ = 0 := hmaxL.fderiv_eq_zero
    have hUii : ∀ i : Fin 4, (iteratedFDeriv ℝ 2 u x₀) ![v i, v i] = lam i := by
      intro i; rw [hdiag i i, if_pos rfl]
    have hCk : ∀ i : Fin 4,
        (∑ k : Fin 4, (fderiv ℝ u x₀) (v k) * (iteratedFDeriv ℝ 2 u x₀) ![v i, v k])
          = (fderiv ℝ u x₀) (v i) * lam i := by
      intro i
      rw [Finset.sum_eq_single i
        (fun k _ hk => by rw [hdiag i k, if_neg (Ne.symm hk), mul_zero])
        (fun h => absurd (Finset.mem_univ i) h)]
      rw [hdiag i i, if_pos rfl]
    -- first order condition
    have hL1 : ∀ i : Fin 4, lam i * (fderiv ℝ u x₀) (v i) =
        (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) *
          (2 * ⟪x₀, v i⟫ / (r ^ 2 - ‖x₀‖ ^ 2)
            - (2 * δ * (u x₀ + C₀)) * (fderiv ℝ u x₀) (v i)) := by
      intro i
      have h := congrArg (fun L : ℝ⁴ →L[ℝ] ℝ => L (v i)) hfderiv0
      simp only [zero_apply] at h
      rw [fderiv_logAux hs hx₀s hu3 (ne_of_gt hqpos) (ne_of_gt hζpos)] at h
      rw [hCk i] at h
      field_simp at h
      field_simp
      linarith [h]
    -- second order condition
    have hL2 : ∀ i : Fin 4, (iteratedFDeriv ℝ 2 (logAux u v r δ C₀) x₀) ![v i, v i] ≤ 0 := by
      intro i
      rw [iteratedFDeriv_two_apply]
      exact Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax hcd hmaxL (v i)
    have hσ2lam : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1 :=
      pair_sum_lam_eq_one hs (hu3.of_le (by norm_num)) hσ2 hx₀s hdiag
    have hσ1 : 0 < ∑ i : Fin 4, lam i := by
      rw [← laplacian_eq_sum_lam hdiag]; exact hΔ x₀ hx₀s
    have hfpos : ∀ i : Fin 4, 0 < (∑ t : Fin 4, lam t) - lam i :=
      Commons.Analysis.Sigma2.linearized_pos_four lam hmono hσ2lam hσ1
    have hfub : ∀ i : Fin 4, (∑ t : Fin 4, lam t) - lam i ≤ (3 / 2) * (∑ t : Fin 4, lam t) :=
      Commons.Analysis.Sigma2.linearized_upper_four lam hmono hσ2lam hσ1
    have hconst := coord_minor_sum_eq_one hs (hu3.of_le (by norm_num)) hσ2 v
    have hthird : ∀ k : Fin 4, (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) *
        (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i]) = 0 :=
      fun k => Commons.Analysis.Sigma2.cofactor_third_diag_sum_zero hs hu3 hx₀s hconst hdiag k
    -- the sum identities
    have hlam2 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * lam i) = 2 := by
      rw [Commons.Analysis.Sigma2.sum_linearized_mul_self, hσ2lam, mul_one]
    have hfs : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)) = 3 * (∑ t : Fin 4, lam t) := by
      have hc : (∑ i : Fin 4, (∑ t : Fin 4, lam t)) = 4 * (∑ t : Fin 4, lam t) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
      rw [Finset.sum_sub_distrib, hc]
      ring
    have hG0 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) *
        (∑ k : Fin 4, (fderiv ℝ u x₀) (v k) * (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i])) = 0 := by
      have hswap : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) *
          (∑ k : Fin 4, (fderiv ℝ u x₀) (v k) * (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i]))
          = ∑ k : Fin 4, (fderiv ℝ u x₀) (v k) *
              (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) *
                (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i]) := by
        have h1 : ∀ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
            * (∑ k : Fin 4, (fderiv ℝ u x₀) (v k) * (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i])
            = ∑ k : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
              * ((fderiv ℝ u x₀) (v k) * (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i]) := by
          intro i; rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [hswap]
      exact Finset.sum_eq_zero (fun k _ => by rw [hthird k, mul_zero])
    have hAnn : 0 ≤ ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
        * (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x₀) ![v k, v i]) ^ 2) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hfpos i))
        (Finset.sum_nonneg (fun k _ => sq_nonneg _)))
    have hXnn : 0 ≤ ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hfpos i)) (sq_nonneg _))
    have hXub : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2)
        ≤ (3 / 2) * (∑ t : Fin 4, lam t) * r ^ 2 := by
      have h2 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2)
          ≤ ∑ i : Fin 4, ((3 / 2) * (∑ t : Fin 4, lam t)) * (⟪x₀, v i⟫) ^ 2 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hfub i) (sq_nonneg _))
      have h3 : (∑ i : Fin 4, ((3 / 2) * (∑ t : Fin 4, lam t)) * (⟪x₀, v i⟫) ^ 2)
          = (3 / 2) * (∑ t : Fin 4, lam t) * (∑ i : Fin 4, (⟪x₀, v i⟫) ^ 2) := by
        rw [← Finset.mul_sum]
      rw [h3, v.sum_sq_inner_left x₀] at h2
      have h5 : ‖x₀‖ ^ 2 ≤ r ^ 2 := by nlinarith [hx₀lt, norm_nonneg x₀, hr]
      nlinarith [h2, h5, hσ1]
    have hB : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * ((fderiv ℝ u x₀) (v i)) ^ 2)
        = (∑ t : Fin 4, lam t) * (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2)
          - ∑ i : Fin 4, lam i * ((fderiv ℝ u x₀) (v i)) ^ 2 := by
      have h1 : ∀ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * ((fderiv ℝ u x₀) (v i)) ^ 2
          = (∑ t : Fin 4, lam t) * ((fderiv ℝ u x₀) (v i)) ^ 2
            - lam i * ((fderiv ℝ u x₀) (v i)) ^ 2 := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hS2 := Commons.Algebra.BigOperators.sum_sq_mul_eq_of_mul_eq
      (f := fun i : Fin 4 => (∑ t : Fin 4, lam t) - lam i)
      (c := fun i : Fin 4 => (fderiv ℝ u x₀) (v i)) (lam := lam)
      (xc := fun i : Fin 4 => ⟪x₀, v i⟫)
      (q := ∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
      (Z := r ^ 2 - ‖x₀‖ ^ 2) (hh := 2 * δ * (u x₀ + C₀))
      (ne_of_gt hζpos) hL1
    have hL2exp : ∀ i : Fin 4,
        (iteratedFDeriv ℝ 2 (logAux u v r δ C₀) x₀) ![v i, v i]
        = (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x₀) ![v k, v i]) ^ 2)
            / (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
          + (∑ k : Fin 4, (fderiv ℝ u x₀) (v k)
              * (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i])
            / (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
          - 2 * ((fderiv ℝ u x₀) (v i) * lam i) ^ 2
            / (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) ^ 2
          + (2 * δ * (u x₀ + C₀)) * lam i
          + 2 * δ * ((fderiv ℝ u x₀) (v i)) ^ 2
          - 2 / (r ^ 2 - ‖x₀‖ ^ 2)
          - 4 * (⟪x₀, v i⟫) ^ 2 / (r ^ 2 - ‖x₀‖ ^ 2) ^ 2 := by
      intro i
      rw [iteratedFDeriv_two_logAux_diag hs hx₀s hu3 (ne_of_gt hqpos) (ne_of_gt hζpos) i,
        hCk i, hUii i]
      ring
    have key := Commons.Algebra.BigOperators.sum_logAux_bound
      (f := fun i : Fin 4 => (∑ t : Fin 4, lam t) - lam i)
      (c := fun i : Fin 4 => (fderiv ℝ u x₀) (v i)) (lam := lam)
      (xc := fun i : Fin 4 => ⟪x₀, v i⟫)
      (A := fun i : Fin 4 => ∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x₀) ![v k, v i]) ^ 2)
      (G := fun i : Fin 4 => ∑ k : Fin 4, (fderiv ℝ u x₀) (v k)
        * (iteratedFDeriv ℝ 3 u x₀) ![v k, v i, v i])
      (L2 := fun i : Fin 4 => (iteratedFDeriv ℝ 2 (logAux u v r δ C₀) x₀) ![v i, v i])
      (q := ∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
      (Z := r ^ 2 - ‖x₀‖ ^ 2) (hh := 2 * δ * (u x₀ + C₀)) (s1 := ∑ t : Fin 4, lam t)
      (δ := δ) (uC := u x₀ + C₀)
      hqpos hζpos hδpos
      (by rw [hC₀]; linarith [(abs_le.mp hubx).1])
      rfl hfpos hL2 hL2exp hAnn hG0 hlam2 hfs hS2
    -- the Cauchy--Schwarz inputs
    have hHnn : 0 ≤ ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * ((fderiv ℝ u x₀) (v i)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hfpos i)) (sq_nonneg _))
    have hcs0 := Commons.Analysis.InnerProductSpace.weighted_cauchy_schwarz
      (fun i : Fin 4 => (∑ t : Fin 4, lam t) - lam i) (fun i : Fin 4 => ⟪x₀, v i⟫)
      (fun i : Fin 4 => (fderiv ℝ u x₀) (v i)) (fun i => le_of_lt (hfpos i))
    have hcs1 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ u x₀) (v i)
        * ⟪x₀, v i⟫) ^ 2
        ≤ (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2)
          * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * ((fderiv ℝ u x₀) (v i)) ^ 2) := by
      have h := hcs0
      rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
        ((∑ t : Fin 4, lam t) - lam i) * ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)
          = ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ u x₀) (v i) * ⟪x₀, v i⟫)] at h
      exact h
    have hcs : -(Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * ((fderiv ℝ u x₀) (v i)) ^ 2)
        * Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2))
        ≤ ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ u x₀) (v i) * ⟪x₀, v i⟫ := by
      have hsq : (Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
            * ((fderiv ℝ u x₀) (v i)) ^ 2)
          * Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2)) ^ 2
          = (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * ((fderiv ℝ u x₀) (v i)) ^ 2)
            * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hHnn, Real.sq_sqrt hXnn]
      have h2 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ u x₀) (v i)
          * ⟪x₀, v i⟫) ^ 2
          ≤ (Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
              * ((fderiv ℝ u x₀) (v i)) ^ 2)
            * Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2)) ^ 2 := by
        rw [hsq]; linarith [hcs1]
      have h3 : |∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ u x₀) (v i)
          * ⟪x₀, v i⟫| ≤ Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
            * ((fderiv ℝ u x₀) (v i)) ^ 2)
          * Real.sqrt (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2) := by
        rw [sq_le_sq] at h2
        rwa [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h2
      linarith [(abs_le.mp h3).1]
    have hWp : (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i))
        ≤ r * Real.sqrt (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) := by
      have hcs2 : (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) ^ 2
          ≤ (∑ i : Fin 4, (⟪x₀, v i⟫) ^ 2) * (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2) := by
        have h := Commons.Analysis.InnerProductSpace.weighted_cauchy_schwarz
          (fun _ : Fin 4 => (1 : ℝ)) (fun i : Fin 4 => ⟪x₀, v i⟫)
          (fun i : Fin 4 => (fderiv ℝ u x₀) (v i)) (fun _ => zero_le_one)
        simpa using h
      have hsq : (‖x₀‖ * Real.sqrt (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2)) ^ 2
          = ‖x₀‖ ^ 2 * (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hqpos.le]
      have h2 : (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) ^ 2
          ≤ (‖x₀‖ * Real.sqrt (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2)) ^ 2 := by
        rw [hsq]
        rw [v.sum_sq_inner_left x₀] at hcs2
        exact hcs2
      have h3 : |∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)|
          ≤ ‖x₀‖ * Real.sqrt (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) := by
        rw [sq_le_sq] at h2
        rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))] at h2
      calc (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i))
          ≤ ‖x₀‖ * Real.sqrt (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) := (abs_le.mp h3).2
        _ ≤ r * Real.sqrt (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_of_lt hx₀lt) (Real.sqrt_nonneg _)
    have hh1 : 2 * δ ≤ 2 * δ * (u x₀ + C₀) := by
      have h1 : (1 : ℝ) ≤ u x₀ + C₀ := by rw [hC₀]; linarith [(abs_le.mp hubx).1]
      nlinarith [hδpos, h1]
    have hh2 : 2 * δ * (u x₀ + C₀) ≤ 4 * δ * C₀ := by
      have h1 : u x₀ + C₀ ≤ 2 * C₀ := by rw [hC₀]; linarith [(abs_le.mp hubx).2]
      nlinarith [hδpos, h1]
    have hZr : r ^ 2 - ‖x₀‖ ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg ‖x₀‖]
    have hL1sum : (∑ i : Fin 4, lam i * ((fderiv ℝ u x₀) (v i)) ^ 2)
        = (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
          * (2 * (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i))
              / (r ^ 2 - ‖x₀‖ ^ 2) - (2 * δ * (u x₀ + C₀))
              * (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)) := by
      have hqq : (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2)
          = (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2) := rfl
      have hpt : ∀ i : Fin 4, lam i * ((fderiv ℝ u x₀) (v i)) ^ 2
          = (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
            * (2 * (⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2)
              - (2 * δ * (u x₀ + C₀)) * ((fderiv ℝ u x₀) (v i)) ^ 2) := by
        intro i
        calc lam i * ((fderiv ℝ u x₀) (v i)) ^ 2
            = (lam i * (fderiv ℝ u x₀) (v i)) * (fderiv ℝ u x₀) (v i) := by ring
          _ = ((∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
                * (2 * ⟪x₀, v i⟫ / (r ^ 2 - ‖x₀‖ ^ 2)
                  - (2 * δ * (u x₀ + C₀)) * (fderiv ℝ u x₀) (v i)))
                * (fderiv ℝ u x₀) (v i) := by rw [hL1 i]
          _ = _ := by ring
      calc (∑ i : Fin 4, lam i * ((fderiv ℝ u x₀) (v i)) ^ 2)
          = ∑ i : Fin 4, (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (2 * (⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2)
                - (2 * δ * (u x₀ + C₀)) * ((fderiv ℝ u x₀) (v i)) ^ 2) :=
              Finset.sum_congr rfl (fun i _ => hpt i)
        _ = ∑ i : Fin 4, ((∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (2 * (⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2))
              - (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
                * ((2 * δ * (u x₀ + C₀)) * ((fderiv ℝ u x₀) (v i)) ^ 2)) :=
              Finset.sum_congr rfl (fun i _ => by ring)
        _ = (∑ i : Fin 4, (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (2 * (⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2)))
            - (∑ i : Fin 4, (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * ((2 * δ * (u x₀ + C₀)) * ((fderiv ℝ u x₀) (v i)) ^ 2)) := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (∑ i : Fin 4, 2 * (⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2))
            - (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (∑ i : Fin 4, (2 * δ * (u x₀ + C₀)) * ((fderiv ℝ u x₀) (v i)) ^ 2) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (2 * (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2))
            - (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * ((2 * δ * (u x₀ + C₀)) * (∑ i : Fin 4, ((fderiv ℝ u x₀) (v i)) ^ 2)) := by
              congr 1
              · rw [← Finset.sum_div, ← Finset.mul_sum]
              · rw [← Finset.mul_sum]
        _ = (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
              * (2 * (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i))
                  / (r ^ 2 - ‖x₀‖ ^ 2)
                - (2 * δ * (u x₀ + C₀))
                  * (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)) := by
              rw [hqq]; ring
    have hL1zero : (∑ i : Fin 4, lam i * ((fderiv ℝ u x₀) (v i)) ^ 2)
        / (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
        + (2 * δ * (u x₀ + C₀)) * (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
        - 2 * (∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i)) / (r ^ 2 - ‖x₀‖ ^ 2) = 0 := by
      rw [hL1sum]
      field_simp
      ring
    have hgrad := Commons.Analysis.Calculus.Bounds.gradient_arith
      (s1 := ∑ t : Fin 4, lam t) (Z := r ^ 2 - ‖x₀‖ ^ 2) (r := r) (C0 := C₀) (δ := δ)
      (hh := 2 * δ * (u x₀ + C₀))
      (B := ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * ((fderiv ℝ u x₀) (v i)) ^ 2)
      (X := ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x₀, v i⟫) ^ 2)
      (Yc := ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ u x₀) (v i) * ⟪x₀, v i⟫)
      (qc := ∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
      (App := ∑ i : Fin 4, lam i * ((fderiv ℝ u x₀) (v i)) ^ 2)
      (Wp := ∑ i : Fin 4, ⟪x₀, v i⟫ * (fderiv ℝ u x₀) (v i))
      hσ1 hζpos hr hC₀1 hδ hh1 hh2 hB hXnn hXub hqpos hcs key hL1zero hWp hZr
    have hsqrt : Real.sqrt (∑ k : Fin 4, ((fderiv ℝ u x₀) (v k)) ^ 2)
        = ‖fderiv ℝ u x₀‖ := by
      rw [← Commons.Analysis.InnerProductSpace.norm_sq_eq_sum_sq_apply v (fderiv ℝ u x₀),
        Real.sqrt_sq (norm_nonneg _)]
    have hbnd : ‖fderiv ℝ u x₀‖ * (r ^ 2 - ‖x₀‖ ^ 2) ≤ 68 * C₀ ^ 2 * r := by
      rw [← hsqrt]; exact hgrad
    have hratio : hfun δ C₀ (u x₀) / hfun δ C₀ (u 0) ≤ 2 := by
      have hexp : hfun δ C₀ (u x₀) / hfun δ C₀ (u 0)
          = Real.exp (δ * (u x₀ + C₀) ^ 2 - δ * (u 0 + C₀) ^ 2) := by
        simp only [hfun, ← Real.exp_sub]
      rw [hexp]
      have h1 : δ * (u x₀ + C₀) ^ 2 - δ * (u 0 + C₀) ^ 2 ≤ 1 / 16 := by
        rw [hδ, hC₀]
        have h2 : (u x₀ + (M + 1)) ^ 2 ≤ (2 * M + 1) ^ 2 := by nlinarith [abs_le.mp hubx]
        have h3 : (0 : ℝ) ≤ (u 0 + (M + 1)) ^ 2 := sq_nonneg _
        have h4 : (2 * M + 1) ^ 2 ≤ 4 * (M + 1) ^ 2 := by nlinarith [hM]
        have h5 : (0 : ℝ) < 1 / (64 * (M + 1) ^ 2) := by positivity
        have h6 : 1 / (64 * (M + 1) ^ 2) * (2 * M + 1) ^ 2 ≤ 1 / 16 := by
          calc 1 / (64 * (M + 1) ^ 2) * (2 * M + 1) ^ 2
              ≤ 1 / (64 * (M + 1) ^ 2) * (4 * (M + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left h4 h5.le
            _ = 1 / 16 := by field_simp; ring
        nlinarith [h2, h3, h5, h6]
      calc Real.exp (δ * (u x₀ + C₀) ^ 2 - δ * (u 0 + C₀) ^ 2) ≤ Real.exp (1 / 16) :=
            Real.exp_le_exp.mpr h1
        _ ≤ 2 := by
            have h : (1 : ℝ) / 16 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
            calc Real.exp (1 / 16) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h
              _ = 2 := Real.exp_log (by norm_num)
    have hmain : ‖fderiv ℝ u 0‖ * r ^ 2 ≤ 136 * C₀ ^ 2 * r := by
      have h2 : ‖fderiv ℝ u 0‖ * hfun δ C₀ (u 0) * r ^ 2
          ≤ ‖fderiv ℝ u x₀‖ * hfun δ C₀ (u x₀) * (r ^ 2 - ‖x₀‖ ^ 2) := by
        rw [← haux0]; exact hmax0
      have h4 : ‖fderiv ℝ u 0‖ * r ^ 2
          ≤ (‖fderiv ℝ u x₀‖ * hfun δ C₀ (u x₀) * (r ^ 2 - ‖x₀‖ ^ 2))
            / hfun δ C₀ (u 0) := by
        rw [le_div_iff₀ (hfun_pos δ C₀ (u 0))]
        linarith [h2]
      have h5 : (‖fderiv ℝ u x₀‖ * hfun δ C₀ (u x₀) * (r ^ 2 - ‖x₀‖ ^ 2))
            / hfun δ C₀ (u 0)
          = ‖fderiv ℝ u x₀‖ * (r ^ 2 - ‖x₀‖ ^ 2)
            * (hfun δ C₀ (u x₀) / hfun δ C₀ (u 0)) := by
        field_simp
      rw [h5] at h4
      have hbz : 0 ≤ ‖fderiv ℝ u x₀‖ * (r ^ 2 - ‖x₀‖ ^ 2) :=
        mul_nonneg (norm_nonneg _) hζpos.le
      have h6 := mul_le_mul_of_nonneg_left hratio hbz
      have h7 : ‖fderiv ℝ u x₀‖ * (r ^ 2 - ‖x₀‖ ^ 2) * 2 ≤ 136 * C₀ ^ 2 * r := by
        nlinarith [hbnd]
      linarith [h4, h6, h7]
    have hfin : ‖fderiv ℝ u 0‖ * r ≤ 512 * (1 + M) ^ 2 := by
      have h8 : (‖fderiv ℝ u 0‖ * r) * r ≤ (136 * C₀ ^ 2) * r := by nlinarith [hmain]
      have h9 : ‖fderiv ℝ u 0‖ * r ≤ 136 * C₀ ^ 2 := (mul_le_mul_iff_of_pos_right hr).mp h8
      have h10 : 136 * C₀ ^ 2 ≤ 512 * (1 + M) ^ 2 := by rw [hC₀]; nlinarith [hM]
      linarith
    exact hfin

open scoped RealInnerProductSpace in
open scoped BigOperators in
/-- **Trudinger's interior gradient estimate (smooth case).**  There is a universal constant `C`
such that every smooth solution `u` of `sigma_2(D^2 u) = 1` with `Delta u > 0` on the ball
`B_r(0)`, with `|u| ≤ M` there, satisfies `|Du(0)| r ≤ C (1 + M)^2`.

The proof is the maximum principle for the auxiliary function
`G(z) = |Du(z)| exp (δ (u z + C₀)^2) (r^2 - |z|^2)`:  the bound at a *smaller* radius `r' < r`
follows from `gradient_bound_of_max`, and one passes to the limit `r' → r`. -/
theorem interior_gradient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ⁴ → ℝ) (r M : ℝ), 0 < r → 0 < M →
      ContDiffOn ℝ 3 u (ball (0 : ℝ⁴) r) → (∀ x ∈ ball (0 : ℝ⁴) r, |u x| ≤ M) →
      (∀ x ∈ ball (0 : ℝ⁴) r, σ₂ (H u (ball (0 : ℝ⁴) r) x) = 1) →
      (∀ x ∈ ball (0 : ℝ⁴) r, 0 < (Δ u) x) →
      ‖fderiv ℝ u 0‖ * r ≤ C * (1 + M) ^ 2 := by
  refine ⟨512, by norm_num, ?_⟩
  intro u r M hr hM hu hub hσ2 hΔ
  have hstep : ∀ r' : ℝ, 0 < r' → r' < r → ‖fderiv ℝ u 0‖ * r' ≤ 512 * (1 + M) ^ 2 := by
    intro r' hr' hr'r
    have hsub : closedBall (0 : ℝ⁴) r' ⊆ ball (0 : ℝ⁴) r := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hcontfd : ContinuousOn (fderiv ℝ u) (closedBall (0 : ℝ⁴) r') :=
      (Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv isOpen_ball
        (hu.of_le (by norm_num))).mono hsub
    have hcontu : ContinuousOn u (closedBall (0 : ℝ⁴) r') :=
      hu.continuousOn.mono hsub
    obtain ⟨x₀, hx₀, hmax⟩ := exists_max_auxFun (u := u) (r := r')
      (δ := 1 / (64 * (M + 1) ^ 2)) (C₀ := M + 1) hr'
      (continuousOn_auxFun hcontfd hcontu)
    exact gradient_bound_of_max (s := ball (0 : ℝ⁴) r) (δ := 1 / (64 * (M + 1) ^ 2))
      (C₀ := M + 1) isOpen_ball hsub hr' hM rfl rfl hu
      (fun x hx => hub x (hsub hx)) hσ2 hΔ hx₀ hmax
  have htend : Tendsto (fun t : ℝ => ‖fderiv ℝ u 0‖ * t) (𝓝[<] r)
      (𝓝 (‖fderiv ℝ u 0‖ * r)) :=
    ((continuous_const.mul continuous_id).continuousAt.tendsto).mono_left inf_le_left
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  by_cases ht0 : 0 < t
  · exact hstep t ht0 ht
  · push_neg at ht0
    have h1 : ‖fderiv ℝ u 0‖ * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) ht0
    have h2 : (0 : ℝ) ≤ 512 * (1 + M) ^ 2 := by positivity
    linarith

end Submission
