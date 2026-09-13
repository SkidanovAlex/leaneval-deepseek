/-
# One-sided stability of the equation `Fop C ε = 0` under a converging family of operators

For Savin's Proposition 4.1 (improvement of flatness) one needs that the limit of a family of
classical solutions `w k` of `Fop (C k) (e k) (D²·) = 0` (with `e k → 0` and `C k → Cstar`) is a
viscosity supersolution of the *linearised* equation `tr (Cstar ∘ D²·) = 0`.

Only the touch-from-BELOW direction is needed, and for that direction the monotonicity of
`Fop C ε` is used only at the TEST function's Hessian (which is bounded); no a priori bound on the
Hessians of the approximating solutions is required.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Mono
import Submission.Savin.Operator
import Submission.Savin.Measure
import Submission.Savin.ContactAbove
import Submission.Savin.Barrier
import Submission.Viscosity
import Submission.Commons.Analysis.Calculus.LocalMax.exists_max_perturb_ball_continuous
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_add_quadratic
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_sub_of_mem_nhds
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_neg_of_mem_nhds
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.quadform_neg_le_of_localMin_paraboloid
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_hessian_op

open Metric MeasureTheory Filter Set
open Commons.Analysis.Calculus.FDeriv Commons.Analysis.Calculus.LocalMax
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

theorem abs_trOp_le (M : ℝ⁴ →L[ℝ] ℝ⁴) : |trOp M| ≤ 4 * ‖M‖ := by
  have h1 : trOp M = ∑ i : Fin 4, ⟪M (stdB4 i), stdB4 i⟫ := trOp_eq_sum M
  calc |trOp M| = |∑ i : Fin 4, ⟪M (stdB4 i), stdB4 i⟫| := by rw [h1]
    _ ≤ ∑ i : Fin 4, |⟪M (stdB4 i), stdB4 i⟫| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, ‖M‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc |⟪M (stdB4 i), stdB4 i⟫| ≤ ‖M (stdB4 i)‖ * ‖stdB4 i‖ := abs_real_inner_le_norm _ _
            _ ≤ (‖M‖ * ‖stdB4 i‖) * ‖stdB4 i‖ := by
                  exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm M _)
                    (norm_nonneg _)
            _ = ‖M‖ := by rw [OrthonormalBasis.norm_eq_one stdB4 i]; ring
    _ = 4 * ‖M‖ := by simp

theorem pairOp_cofOp_lower (M : ℝ⁴ →L[ℝ] ℝ⁴) (v : ℝ⁴) :
    -(5 * ‖M‖ * ‖v‖ ^ 2) ≤ ⟪cofOp M v, v⟫ := by
  have h1 : cofOp M = trOp M • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - M := rfl
  have h2 : ⟪cofOp M v, v⟫ = trOp M * ‖v‖ ^ 2 - ⟪M v, v⟫ := by
    rw [h1, sub_apply, inner_sub_left, ContinuousLinearMap.smul_apply, real_inner_smul_left,
      ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq]
  have h3 : ⟪M v, v⟫ ≤ ‖M‖ * ‖v‖ ^ 2 := by
    have h4 : |⟪M v, v⟫| ≤ ‖M v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    have h5 : ‖M v‖ ≤ ‖M‖ * ‖v‖ := ContinuousLinearMap.le_opNorm M v
    have h6 : ⟪M v, v⟫ ≤ |⟪M v, v⟫| := le_abs_self _
    have h7 : ‖M v‖ * ‖v‖ ≤ (‖M‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right h5 (norm_nonneg v)
    have h8 : (‖M‖ * ‖v‖) * ‖v‖ = ‖M‖ * ‖v‖ ^ 2 := by ring
    linarith
  have h6 : -(4 * ‖M‖) ≤ trOp M := by
    have := abs_trOp_le M
    rw [abs_le] at this
    exact this.1
  rw [h2]
  have h7 : -(4 * ‖M‖) * ‖v‖ ^ 2 ≤ trOp M * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h6 (sq_nonneg _)
  linarith

/-! ## One-sided stability of `Fop C ε = 0` under a converging family

For Savin's Proposition 4.1 (improvement of flatness) one needs that the limit of a family of
classical solutions `w k` of `Fop (C k) (e k) (D²·) = 0` (with `e k → 0` and `C k → Cstar`) is a
viscosity supersolution of the linearised equation `tr (Cstar ∘ D²·) = 0`: at a strictly
below-touching test function `ψ`, one has `tr(Cstar ∘ D²ψ) ≤ 0`.

Only the touch-from-BELOW direction is needed, and for it the monotonicity `Fop_mono` is applied at
the TEST function's Hessian (which is bounded); no a priori bound on the Hessians of the
approximating solutions is required.
-/

/-- The `♯`-operation (bounded bilinear form ↦ operator) does not increase the norm. -/
theorem norm_continuousLinearMapOfBilin_le (B : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) :
    ‖InnerProductSpace.continuousLinearMapOfBilin B‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun v => ?_
  rcases eq_or_ne (InnerProductSpace.continuousLinearMapOfBilin B v) 0 with h0 | h0
  · rw [h0, norm_zero]; positivity
  · have hn : 0 < ‖InnerProductSpace.continuousLinearMapOfBilin B v‖ := norm_pos_iff.mpr h0
    have h1 : ‖InnerProductSpace.continuousLinearMapOfBilin B v‖ ^ 2
        = B v (InnerProductSpace.continuousLinearMapOfBilin B v) := by
      rw [← real_inner_self_eq_norm_sq, InnerProductSpace.continuousLinearMapOfBilin_apply]
    have h2 : B v (InnerProductSpace.continuousLinearMapOfBilin B v)
        ≤ ‖B v‖ * ‖InnerProductSpace.continuousLinearMapOfBilin B v‖ := by
      calc B v (InnerProductSpace.continuousLinearMapOfBilin B v)
          ≤ |B v (InnerProductSpace.continuousLinearMapOfBilin B v)| := le_abs_self _
        _ = ‖B v (InnerProductSpace.continuousLinearMapOfBilin B v)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖B v‖ * ‖InnerProductSpace.continuousLinearMapOfBilin B v‖ :=
            ContinuousLinearMap.le_opNorm (B v) _
    have h3 : ‖B v‖ ≤ ‖B‖ * ‖v‖ := ContinuousLinearMap.le_opNorm B v
    have h4 : ‖InnerProductSpace.continuousLinearMapOfBilin B v‖ ^ 2
        ≤ (‖B‖ * ‖v‖) * ‖InnerProductSpace.continuousLinearMapOfBilin B v‖ := by
      rw [h1]
      exact h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
    nlinarith [h4, hn, norm_nonneg (InnerProductSpace.continuousLinearMapOfBilin B v),
      norm_nonneg B, norm_nonneg v]

/-- The second Fréchet derivative operator is additive under subtraction. -/
theorem hessOp_sub_of_contDiffAt {φ ψ : ℝ⁴ → ℝ} {x : ℝ⁴}
    (hφ : ContDiffAt ℝ 2 φ x) (hψ : ContDiffAt ℝ 2 ψ x) :
    hessOp (φ - ψ) x = hessOp φ x - hessOp ψ x := by
  have hsub : ContDiffAt ℝ 2 (φ - ψ) x := hφ.sub hψ
  refine clm_eq_of_inner_self_eq (hessOp_symm_of_contDiffAt hsub)
    ((hessOp_symm_of_contDiffAt hφ).sub (hessOp_symm_of_contDiffAt hψ)) fun v => ?_
  have h1 : ⟪hessOp (φ - ψ) x v, v⟫ = (fderiv ℝ (fderiv ℝ (φ - ψ)) x) v v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply (B := fderiv ℝ (fderiv ℝ (φ - ψ)) x) v v
  have h2 : ⟪hessOp φ x v, v⟫ = (fderiv ℝ (fderiv ℝ φ) x) v v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply (B := fderiv ℝ (fderiv ℝ φ) x) v v
  have h3 : ⟪hessOp ψ x v, v⟫ = (fderiv ℝ (fderiv ℝ ψ) x) v v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply (B := fderiv ℝ (fderiv ℝ ψ) x) v v
  have h4 : (fderiv ℝ (fderiv ℝ (φ - ψ)) x) v v
      = (fderiv ℝ (fderiv ℝ φ) x) v v - (fderiv ℝ (fderiv ℝ ψ) x) v v := by
    rw [Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_sub_of_contDiffAt hφ hψ]
    simp only [sub_apply]
  have h5 : ⟪(hessOp φ x - hessOp ψ x) v, v⟫
      = ⟪hessOp φ x v, v⟫ - ⟪hessOp ψ x v, v⟫ := by
    rw [sub_apply, inner_sub_left]
  rw [h1, h4, h5, h2, h3]

/-- `pairOp` is bounded by the product of the operator norms. -/
theorem abs_pairOp_le (S M : ℝ⁴ →L[ℝ] ℝ⁴) : |pairOp S M| ≤ 4 * ‖S‖ * ‖M‖ := by
  have h1 : pairOp S M = trOp (S * M) := by
    rw [pairOp_eq_trace, trOp]
    rfl
  have h2 : ‖S * M‖ ≤ ‖S‖ * ‖M‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : (S * M) v = S (M v) := rfl
    rw [hv]
    calc ‖S (M v)‖ ≤ ‖S‖ * ‖M v‖ := ContinuousLinearMap.le_opNorm S _
      _ ≤ ‖S‖ * (‖M‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm M v) (norm_nonneg S)
      _ = (‖S‖ * ‖M‖) * ‖v‖ := by ring
  rw [h1]
  calc |trOp (S * M)| ≤ 4 * ‖S * M‖ := abs_trOp_le _
    _ ≤ 4 * (‖S‖ * ‖M‖) := by linarith [h2]
    _ = 4 * ‖S‖ * ‖M‖ := by ring

/-- A bound for the quadratic model of `σ₂` in terms of the operator norm. -/
theorem abs_s2_le (M : ℝ⁴ →L[ℝ] ℝ⁴) : |s2 M| ≤ 32 * ‖M‖ ^ 2 := by
  have hM : ∀ i j : Fin 4, |⟪M (stdB4 i), stdB4 j⟫| ≤ ‖M‖ := by
    intro i j
    calc |⟪M (stdB4 i), stdB4 j⟫| ≤ ‖M (stdB4 i)‖ * ‖stdB4 j‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖M‖ * ‖stdB4 i‖) * ‖stdB4 j‖ := by
            exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm M _) (norm_nonneg _)
      _ = ‖M‖ := by rw [OrthonormalBasis.norm_eq_one stdB4 i,
            OrthonormalBasis.norm_eq_one stdB4 j]; ring
  have hterm : ∀ i j : Fin 4,
      |(if i < j then (⟪M (stdB4 i), stdB4 i⟫ * ⟪M (stdB4 j), stdB4 j⟫
        - ⟪M (stdB4 i), stdB4 j⟫ ^ 2) else 0)| ≤ 2 * ‖M‖ ^ 2 := by
    intro i j
    by_cases hij : i < j
    · rw [if_pos hij]
      have h1 : |⟪M (stdB4 i), stdB4 i⟫ * ⟪M (stdB4 j), stdB4 j⟫| ≤ ‖M‖ ^ 2 := by
        rw [abs_mul, pow_two]
        exact mul_le_mul (hM i i) (hM j j) (abs_nonneg _) (norm_nonneg _)
      have h2 : |⟪M (stdB4 i), stdB4 j⟫ ^ 2| ≤ ‖M‖ ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM i j) 2
      calc |⟪M (stdB4 i), stdB4 i⟫ * ⟪M (stdB4 j), stdB4 j⟫ - ⟪M (stdB4 i), stdB4 j⟫ ^ 2|
          ≤ |⟪M (stdB4 i), stdB4 i⟫ * ⟪M (stdB4 j), stdB4 j⟫|
            + |⟪M (stdB4 i), stdB4 j⟫ ^ 2| := abs_sub _ _
        _ ≤ ‖M‖ ^ 2 + ‖M‖ ^ 2 := add_le_add h1 h2
        _ = 2 * ‖M‖ ^ 2 := by ring
    · rw [if_neg hij, abs_zero]
      have : (0:ℝ) ≤ ‖M‖ ^ 2 := sq_nonneg _
      linarith
  unfold s2
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hterm i j) ?_
  refine le_of_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Any vector is bounded by the sum of the absolute values of its coordinates. -/
theorem norm_le_sum_inner_vec (x : ℝ⁴) : ‖x‖ ≤ ∑ j : Fin 4, |⟪x, stdB4 j⟫| := by
  have hx : ∑ j : Fin 4, ⟪stdB4 j, x⟫ • stdB4 j = x := by
    simpa [OrthonormalBasis.repr_apply_apply] using OrthonormalBasis.sum_repr stdB4 x
  calc ‖x‖ = ‖∑ j : Fin 4, ⟪stdB4 j, x⟫ • stdB4 j‖ := by rw [hx]
    _ ≤ ∑ j : Fin 4, ‖⟪stdB4 j, x⟫ • stdB4 j‖ := norm_sum_le _ _
    _ = ∑ j : Fin 4, |⟪stdB4 j, x⟫| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one stdB4 j, mul_one]
    _ = ∑ j : Fin 4, |⟪x, stdB4 j⟫| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_comm]

/-- An operator is bounded by the sum of the absolute values of its matrix entries. -/
theorem norm_le_sum_abs_inner (M : ℝ⁴ →L[ℝ] ℝ⁴) :
    ‖M‖ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |⟪M (stdB4 i), stdB4 j⟫| := by
  have hnn : (0:ℝ) ≤ ∑ i : Fin 4, ∑ j : Fin 4, |⟪M (stdB4 i), stdB4 j⟫| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
  have hv : M v = ∑ i : Fin 4, ⟪stdB4 i, v⟫ • M (stdB4 i) := by
    have h := congrArg M (show ∑ i : Fin 4, ⟪stdB4 i, v⟫ • stdB4 i = v from by
      simpa [OrthonormalBasis.repr_apply_apply] using OrthonormalBasis.sum_repr stdB4 v)
    simpa using h.symm
  calc ‖M v‖ = ‖∑ i : Fin 4, ⟪stdB4 i, v⟫ • M (stdB4 i)‖ := by rw [hv]
    _ ≤ ∑ i : Fin 4, ‖⟪stdB4 i, v⟫ • M (stdB4 i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, |⟪stdB4 i, v⟫| * ‖M (stdB4 i)‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin 4, ‖v‖ * ∑ j : Fin 4, |⟪M (stdB4 i), stdB4 j⟫| := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul ?_ (norm_le_sum_inner_vec (M (stdB4 i))) (norm_nonneg _)
          (norm_nonneg v)
        calc |⟪stdB4 i, v⟫| ≤ ‖stdB4 i‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ = ‖v‖ := by rw [OrthonormalBasis.norm_eq_one stdB4 i, one_mul]
    _ = (∑ i : Fin 4, ∑ j : Fin 4, |⟪M (stdB4 i), stdB4 j⟫|) * ‖v‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]

/-- **One-sided stability of `Fop C ε = 0`** (the touch-from-below half of the viscosity
supersolution property of the limit).

Let `w k` be classical solutions of `Fop (C k) (e k) (D²·) = 0` on an open set `s`, with `C k → Cstar`
and `e k → 0`, converging locally uniformly to `g`.  Suppose that `C k ⪰ c/2` and that the quadratic
coefficient `e k` is so small that `Fop (C k) (e k)` is increasing on the ball of radius `B`, and
that a `C²` test function `ψ` with `‖D²ψ‖ + 3 ≤ B` touches `g` *strictly from below* at `x₀`.  Then
`tr (Cstar ∘ D²ψ(x₀)) ≤ 0`. -/
theorem pairOp_le_of_strictTouchFromBelow
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c B : ℝ}
    (hs : IsOpen s) (hc : 0 < c)
    (he0 : ∀ k, 0 ≤ e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hCk : ∀ k v, c / 2 * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (heB : ∀ᶠ k in atTop, 5 * B * e k ≤ c / 2) (hB2 : 2 ≤ B)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    {ψ : ℝ⁴ → ℝ} (hψ : ContDiffOn ℝ 2 ψ s) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (hBψ : ∀ x ∈ s, ‖hessOp ψ x‖ + 3 ≤ B)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, y ≠ x₀ → g x₀ - ψ x₀ < g y - ψ y) :
    pairOp Cstar (hessOp ψ x₀) ≤ 0 := by
  classical
  -- ## Step 1: a ball around `x₀` contained in `s`, on which `ψ` touches `g` strictly
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := mem_nhdsWithin_iff.mp htouch
  set R : ℝ := min (ε₀ / 2) (ρ₁ / 2) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (by linarith)
  have hRε : R < ε₀ := by rw [hRdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRρ : R < ρ₁ := by rw [hRdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hRs : closedBall x₀ R ⊆ s := fun y hy => hε₀sub (by
    rw [mem_ball]
    have h := mem_closedBall.mp hy
    have h2 : dist y x₀ ≤ R := by
      have h3 := dist_comm x₀ y
      linarith
    linarith)
  have hstrict : ∀ y ∈ closedBall x₀ R, y ≠ x₀ → g x₀ - ψ x₀ < g y - ψ y := by
    intro y hy hyne
    refine hρ₁sub ⟨?_, hRs hy⟩ hyne
    rw [mem_ball]
    have h := mem_closedBall.mp hy
    have h2 : dist y x₀ ≤ R := by
      have h3 := dist_comm x₀ y
      linarith
    linarith
  -- ## Step 2: continuity of the limit on the closed ball
  have hK : IsCompact (closedBall x₀ R) := isCompact_closedBall x₀ R
  have hconvK := hconv _ hRs hK
  have hgc : ContinuousOn g (closedBall x₀ R) :=
    hconvK.continuousOn (Filter.Frequently.of_forall fun k => ((hw2 k).continuousOn).mono hRs)
  have hgcψ : ContinuousOn (fun y => g y - ψ y) (closedBall x₀ R) :=
    hgc.sub ((hψ.continuousOn).mono hRs)
  -- ## Step 3: minimisers of `w k - ψ` on the closed ball
  have hcont : ∀ k, ContinuousOn (fun y => w k y - ψ y) (closedBall x₀ R) := fun k =>
    (((hw2 k).continuousOn).mono hRs).sub ((hψ.continuousOn).mono hRs)
  choose xk hxkmem hxkmin using fun k =>
    hK.exists_isMinOn ⟨x₀, mem_closedBall_self hRpos.le⟩ (hcont k)
  have hxkmin' : ∀ k, ∀ y ∈ closedBall x₀ R, w k (xk k) - ψ (xk k) ≤ w k y - ψ y :=
    fun k => hxkmin k
  -- ## Step 4: `xk → x₀`
  have hxk_tend : Tendsto xk atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    rw [← Filter.eventually_atTop]
    by_contra h
    rw [Filter.not_eventually] at h
    have hfr : ∃ᶠ k in atTop, δ ≤ dist (xk k) x₀ := h.mono fun k hk => not_lt.mp hk
    have hAcomp : IsCompact (closedBall x₀ R ∩ {y : ℝ⁴ | δ ≤ dist y x₀}) :=
      hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
    obtain ⟨k₁, hk₁⟩ := hfr.exists
    obtain ⟨a, haA, hamin⟩ := hAcomp.exists_isMinOn
      ⟨xk k₁, hxkmem k₁, hk₁⟩ (hgcψ.mono Set.inter_subset_left)
    have ha_ne : a ≠ x₀ := by
      intro h'
      have h2 : δ ≤ dist x₀ x₀ := h' ▸ haA.2
      simp at h2
      linarith
    have hgap : g x₀ - ψ x₀ < g a - ψ a := hstrict a haA.1 ha_ne
    have hamin' : ∀ y ∈ closedBall x₀ R ∩ {y : ℝ⁴ | δ ≤ dist y x₀},
        g a - ψ a ≤ g y - ψ y := hamin
    set η : ℝ := (g a - ψ a - (g x₀ - ψ x₀)) / 3 with hηdef
    have hηpos : 0 < η := by rw [hηdef]; linarith
    have hev := (tendstoUniformlyOn_iff.mp hconvK) η hηpos
    obtain ⟨k₂, hk₂⟩ := (hfr.and_eventually hev).exists
    have h1 : g a - ψ a ≤ g (xk k₂) - ψ (xk k₂) := hamin' _ ⟨hxkmem k₂, hk₂.1⟩
    have h2 : g (xk k₂) ≤ w k₂ (xk k₂) + η := by
      have h := hk₂.2 (xk k₂) (hxkmem k₂)
      rw [Real.dist_eq] at h
      have h' := (abs_lt.mp h).2
      linarith
    have h3 : w k₂ (xk k₂) - ψ (xk k₂) ≤ w k₂ x₀ - ψ x₀ :=
      hxkmin' k₂ x₀ (mem_closedBall_self hRpos.le)
    have h4 : w k₂ x₀ ≤ g x₀ + η := by
      have h := hk₂.2 x₀ (mem_closedBall_self hRpos.le)
      rw [Real.dist_eq] at h
      have h' := (abs_lt.mp h).1
      linarith
    have h5 : g a - ψ a ≤ (g x₀ - ψ x₀) + 2 * η := by linarith
    rw [hηdef] at h5
    linarith
  -- ## Step 5: for large `k`, the minimiser is an interior local minimum
  have hxk_int : ∀ᶠ k in atTop, xk k ∈ ball x₀ R :=
    hxk_tend.eventually (isOpen_ball.mem_nhds (mem_ball_self hRpos))
  have hmin_ev : ∀ᶠ k in atTop, IsLocalMin (fun y => w k y - ψ y) (xk k) := by
    filter_upwards [hxk_int] with k hk
    rw [IsLocalMin, IsMinFilter]
    filter_upwards [isOpen_ball.mem_nhds hk] with y hy
    exact hxkmin' k y (ball_subset_closedBall hy)
  -- ## Step 6: the monotonicity step
  have hfle : ∀ᶠ k in atTop, Fop (C k) (e k) (hessOp ψ (xk k)) ≤ 0 := by
    filter_upwards [hmin_ev, heB] with k hmin hBk
    have hak : xk k ∈ s := hRs (hxkmem k)
    have hwk : ContDiffAt ℝ 2 (w k) (xk k) := (hw2 k).contDiffAt (hs.mem_nhds hak)
    have hψk : ContDiffAt ℝ 2 ψ (xk k) := hψ.contDiffAt (hs.mem_nhds hak)
    have hq : ∀ v : ℝ⁴, 0 ≤ ⟪(hessOp (w k) (xk k) - hessOp ψ (xk k)) v, v⟫ := by
      intro v
      have h1 : 0 ≤ (fderiv ℝ (fderiv ℝ (w k - ψ)) (xk k)) v v :=
        Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
          (hwk.sub hψk) hmin v
      have h2 : (fderiv ℝ (fderiv ℝ (w k - ψ)) (xk k)) v v
          = ⟪hessOp (w k - ψ) (xk k) v, v⟫ := by
        rw [show hessOp (w k - ψ) (xk k) = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ (w k - ψ)) (xk k)) from rfl]
        exact (InnerProductSpace.continuousLinearMapOfBilin_apply _ v v).symm
      rw [h2, hessOp_sub_of_contDiffAt hwk hψk] at h1
      exact h1
    have hCT : ∀ v : ℝ⁴, 0 ≤ ⟪(C k + e k • cofOp (hessOp ψ (xk k))) v, v⟫ := by
      intro v
      have h1 : c / 2 * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫ := hCk k v
      have h2 : -(5 * ‖hessOp ψ (xk k)‖ * ‖v‖ ^ 2)
          ≤ ⟪cofOp (hessOp ψ (xk k)) v, v⟫ := pairOp_cofOp_lower _ v
      have h3 : ‖hessOp ψ (xk k)‖ ≤ B := by
        have := hBψ (xk k) hak
        linarith
      have h5 : e k * (-(5 * ‖hessOp ψ (xk k)‖ * ‖v‖ ^ 2))
          ≤ e k * ⟪cofOp (hessOp ψ (xk k)) v, v⟫ :=
        mul_le_mul_of_nonneg_left h2 (he0 k)
      have h6 : e k * (5 * ‖hessOp ψ (xk k)‖ * ‖v‖ ^ 2) ≤ e k * (5 * B * ‖v‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (he0 k)
        nlinarith [sq_nonneg ‖v‖]
      have h7 : ⟪(C k + e k • cofOp (hessOp ψ (xk k))) v, v⟫
          = ⟪C k v, v⟫ + e k * ⟪cofOp (hessOp ψ (xk k)) v, v⟫ := by
        rw [add_apply, inner_add_left, smul_apply, real_inner_smul_left]
      rw [h7]
      nlinarith [h1, h5, h6, hBk, sq_nonneg ‖v‖]
    have hmono := Fop_mono (hCsym k) (he0 k) (hessOp_symm_of_contDiffAt hwk)
      (hessOp_symm_of_contDiffAt hψk) hq hCT
    rw [heq k (xk k) hak] at hmono
    exact hmono
  -- ## Step 7: pass to the limit along `k → ∞`
  have hAcont : ContinuousAt (fun x => fderiv ℝ (fderiv ℝ ψ) x) x₀ :=
    ((hψ.contDiffAt (hs.mem_nhds hx₀)).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv
      (by norm_num)
  have hAtend : Tendsto (fun k => fderiv ℝ (fderiv ℝ ψ) (xk k)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ ψ) x₀)) := hAcont.tendsto.comp hxk_tend
  have heval : ∀ i j : Fin 4,
      Tendsto (fun k => fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j))) := by
    intro i j
    have hcontEval : Continuous (fun M : ℝ⁴ →L[ℝ] (ℝ⁴ →L[ℝ] ℝ) =>
        M (stdB4 i) (stdB4 j)) :=
      ((ContinuousLinearMap.apply ℝ ℝ (stdB4 j)).continuous.comp
        (ContinuousLinearMap.apply ℝ (ℝ⁴ →L[ℝ] ℝ) (stdB4 i)).continuous)
    exact (hcontEval.tendsto (fderiv ℝ (fderiv ℝ ψ) x₀)).comp hAtend
  have hterm : ∀ i j : Fin 4, Tendsto (fun k =>
      |fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)
        - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) atTop (𝓝 0) := by
    intro i j
    have h1 : Tendsto (fun _ : ℕ => fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j))) := tendsto_const_nhds
    have h := ((heval i j).sub h1).abs
    simpa using h
  have hscl : Tendsto (fun k => ∑ i : Fin 4, ∑ j : Fin 4,
      |fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)
        - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) atTop (𝓝 0) := by
    have h := tendsto_finset_sum Finset.univ
      (fun i _ => tendsto_finset_sum Finset.univ (fun j _ => hterm i j))
    simpa using h
  have hMdiff : ∀ k, ‖hessOp ψ (xk k) - hessOp ψ x₀‖
      ≤ ∑ i : Fin 4, ∑ j : Fin 4,
          |fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)
            - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| := by
    intro k
    have h1 : hessOp ψ (xk k) - hessOp ψ x₀
        = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ ψ) (xk k) - fderiv ℝ (fderiv ℝ ψ) x₀) := by
      rw [show hessOp ψ (xk k) = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ ψ) (xk k)) from rfl,
          show hessOp ψ x₀ = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ ψ) x₀) from rfl,
          Commons.Analysis.Calculus.FDeriv.continuousLinearMapOfBilin_sub]
    rw [h1]
    refine le_trans (norm_le_sum_abs_inner _) ?_
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
    have h2 : (fderiv ℝ (fderiv ℝ ψ) (xk k) - fderiv ℝ (fderiv ℝ ψ) x₀)
        (stdB4 i) (stdB4 j)
        = fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j) := by
      simp only [sub_apply]
    rw [h2]
  have hMbound : ∀ k, ‖hessOp ψ (xk k)‖ ≤ B := by
    intro k
    have := hBψ (xk k) (hRs (hxkmem k))
    linarith
  have hCsub : Tendsto (fun k => C k - Cstar) atTop (𝓝 0) := by
    have h1 : Tendsto (fun _ : ℕ => Cstar) atTop (𝓝 Cstar) := tendsto_const_nhds
    have h := hCtend.sub h1
    simpa using h
  have ht1 : Tendsto (fun k => pairOp (C k - Cstar) (hessOp ψ (xk k))) atTop (𝓝 0) := by
    have ha : Tendsto (fun k => 4 * B * ‖C k - Cstar‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => ‖C k - Cstar‖) atTop (𝓝 0) := by
        simpa using hCsub.norm
      have h := h0.const_mul (4 * B)
      simpa using h
    refine squeeze_zero_norm' (a := fun k => 4 * B * ‖C k - Cstar‖) ?_ ha
    filter_upwards with k
    calc ‖pairOp (C k - Cstar) (hessOp ψ (xk k))‖
        = |pairOp (C k - Cstar) (hessOp ψ (xk k))| := Real.norm_eq_abs _
      _ ≤ 4 * ‖C k - Cstar‖ * ‖hessOp ψ (xk k)‖ := abs_pairOp_le _ _
      _ ≤ 4 * ‖C k - Cstar‖ * B :=
          mul_le_mul_of_nonneg_left (hMbound k) (by positivity)
      _ = 4 * B * ‖C k - Cstar‖ := by ring
  have ht2 : Tendsto (fun k => pairOp Cstar (hessOp ψ (xk k) - hessOp ψ x₀))
      atTop (𝓝 0) := by
    have ha : Tendsto (fun k => 4 * ‖Cstar‖ * (∑ i : Fin 4, ∑ j : Fin 4,
        |fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|)) atTop (𝓝 0) := by
      have h := hscl.const_mul (4 * ‖Cstar‖)
      simpa using h
    refine squeeze_zero_norm' (a := fun k => 4 * ‖Cstar‖ * (∑ i : Fin 4, ∑ j : Fin 4,
        |fderiv ℝ (fderiv ℝ ψ) (xk k) (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|)) ?_ ha
    filter_upwards with k
    calc ‖pairOp Cstar (hessOp ψ (xk k) - hessOp ψ x₀)‖
        = |pairOp Cstar (hessOp ψ (xk k) - hessOp ψ x₀)| := Real.norm_eq_abs _
      _ ≤ 4 * ‖Cstar‖ * ‖hessOp ψ (xk k) - hessOp ψ x₀‖ := abs_pairOp_le _ _
      _ ≤ 4 * ‖Cstar‖ * _ := mul_le_mul_of_nonneg_left (hMdiff k) (by positivity)
  have ht3 : Tendsto (fun k => e k * s2 (hessOp ψ (xk k))) atTop (𝓝 0) := by
    have ha : Tendsto (fun k => |e k| * (32 * B ^ 2)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => |e k|) atTop (𝓝 0) := by
        simpa using hetend.abs
      have h := h0.mul_const (32 * B ^ 2)
      simpa using h
    refine squeeze_zero_norm' (a := fun k => |e k| * (32 * B ^ 2)) ?_ ha
    filter_upwards with k
    have hb : ‖hessOp ψ (xk k)‖ ≤ B := hMbound k
    calc ‖e k * s2 (hessOp ψ (xk k))‖ = |e k * s2 (hessOp ψ (xk k))| := Real.norm_eq_abs _
      _ = |e k| * |s2 (hessOp ψ (xk k))| := abs_mul _ _
      _ ≤ |e k| * (32 * ‖hessOp ψ (xk k)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_s2_le _) (abs_nonneg _)
      _ ≤ |e k| * (32 * B ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hB0 : 0 ≤ B := by linarith
          nlinarith [hb, norm_nonneg (hessOp ψ (xk k))]
  have hmix : Tendsto (fun k => pairOp (C k - Cstar) (hessOp ψ (xk k))
      + (pairOp Cstar (hessOp ψ (xk k) - hessOp ψ x₀) + e k * s2 (hessOp ψ (xk k))))
      atTop (𝓝 0) := by
    have h := ht1.add (ht2.add ht3)
    simpa using h
  have hflim : Tendsto (fun k => Fop (C k) (e k) (hessOp ψ (xk k))) atTop
      (𝓝 (pairOp Cstar (hessOp ψ x₀))) := by
    have hkey : (fun k => pairOp (C k - Cstar) (hessOp ψ (xk k))
        + (pairOp Cstar (hessOp ψ (xk k) - hessOp ψ x₀) + e k * s2 (hessOp ψ (xk k))))
        = fun k => Fop (C k) (e k) (hessOp ψ (xk k)) - pairOp Cstar (hessOp ψ x₀) := by
      funext k
      have h1 : pairOp (C k) (hessOp ψ (xk k))
          = pairOp (C k - Cstar) (hessOp ψ (xk k)) + pairOp Cstar (hessOp ψ (xk k)) := by
        have he : C k = C k - Cstar + Cstar := by abel
        conv_lhs => rw [he]
        rw [pairOp_add_left]
      have h2 : pairOp Cstar (hessOp ψ (xk k))
          = pairOp Cstar (hessOp ψ (xk k) - hessOp ψ x₀) + pairOp Cstar (hessOp ψ x₀) := by
        have he : hessOp ψ (xk k) = (hessOp ψ (xk k) - hessOp ψ x₀) + hessOp ψ x₀ := by abel
        conv_lhs => rw [he]
        rw [pairOp_add]
      unfold Fop
      rw [h1, h2]
      ring
    rw [hkey] at hmix
    have h := hmix.add_const (pairOp Cstar (hessOp ψ x₀))
    have h' : (fun k => (Fop (C k) (e k) (hessOp ψ (xk k)) - pairOp Cstar (hessOp ψ x₀))
        + pairOp Cstar (hessOp ψ x₀)) = fun k => Fop (C k) (e k) (hessOp ψ (xk k)) := by
      funext k; ring
    rw [h'] at h
    simpa using h
  exact le_of_tendsto hflim hfle

/-- **One-sided stability, non-strict touching version.**  Same as
`pairOp_le_of_strictTouchFromBelow` but with a non-strict touching condition; obtained by applying
the strict version to the perturbed test function `ψ - δ‖·-x₀‖²` and letting `δ → 0⁺`. -/
theorem pairOp_le_of_touchFromBelow
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c B : ℝ}
    (hs : IsOpen s) (hc : 0 < c)
    (he0 : ∀ k, 0 ≤ e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hCk : ∀ k v, c / 2 * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (heB : ∀ᶠ k in atTop, 5 * B * e k ≤ c / 2) (hB2 : 2 ≤ B)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    {ψ : ℝ⁴ → ℝ} (hψ : ContDiffOn ℝ 2 ψ s) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (hBψ : ∀ x ∈ s, ‖hessOp ψ x‖ + 5 ≤ B)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, g x₀ - ψ x₀ ≤ g y - ψ y) :
    pairOp Cstar (hessOp ψ x₀) ≤ 0 := by
  classical
  have hmain : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      pairOp Cstar (hessOp ψ x₀) ≤ 2 * δ * trOp Cstar := by
    intro δ hδpos hδ1
    set ψδ : ℝ⁴ → ℝ := fun y => ψ y + parab (2 * δ) x₀ 0 y with hψδdef
    have hψδeq : ∀ y : ℝ⁴, ψδ y = ψ y - δ * ‖y - x₀‖ ^ 2 := by
      intro y
      simp only [hψδdef, parab_apply]
      ring
    have hψδ2 : ContDiffOn ℝ 2 ψδ s := by
      refine (hψ.add ?_)
      exact ((contDiff_parab (2 * δ) 0 x₀).contDiffOn).of_le (m := 2)
        (WithTop.coe_le_coe.mpr le_top)
    have hBψδ : ∀ x ∈ s, ‖hessOp ψδ x‖ + 3 ≤ B := by
      intro x hx
      have h1 : ψδ = fun y => ψ y + parab (2 * δ) x₀ 0 y := hψδdef
      have hψat : ContDiffAt ℝ 2 ψ x := hψ.contDiffAt (hs.mem_nhds hx)
      have hpat : ContDiffAt ℝ 2 (parab (2 * δ) x₀ 0) x :=
        ((contDiff_parab (2 * δ) 0 x₀).contDiffAt).of_le (m := 2)
          (WithTop.coe_le_coe.mpr le_top)
      have hhess : hessOp ψδ x = hessOp ψ x + hessOp (parab (2 * δ) x₀ 0) x := by
        rw [h1]
        exact hessOp_add hψat hpat
      have hpar : hessOp (parab (2 * δ) x₀ 0) x = (-(2 * δ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) :=
        hessOp_parab (2 * δ) 0 x₀ x
      have hnorm : ‖hessOp ψδ x‖ ≤ ‖hessOp ψ x‖ + 2 * δ := by
        rw [hhess, hpar]
        calc ‖hessOp ψ x + (-(2 * δ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖
            ≤ ‖hessOp ψ x‖ + ‖(-(2 * δ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖ := norm_add_le _ _
          _ = ‖hessOp ψ x‖ + 2 * δ := by
              rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one, abs_neg,
                abs_of_pos (by positivity : (0:ℝ) < 2 * δ)]
      have h5 : ‖hessOp ψδ x‖ + 3 ≤ B := by
        have := hBψ x hx
        linarith
      exact h5
    have htouchδ : ∀ᶠ y in 𝓝[s] x₀, y ≠ x₀ →
        g x₀ - ψδ x₀ < g y - ψδ y := by
      filter_upwards [htouch] with y hy hyne
      have h1 : ψδ x₀ = ψ x₀ := by rw [hψδeq]; simp
      have h2 : g y - ψδ y = g y - ψ y + δ * ‖y - x₀‖ ^ 2 := by
        rw [hψδeq y]; ring
      have hpos : 0 < δ * ‖y - x₀‖ ^ 2 := by
        have : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
        positivity
      rw [h1, h2]
      linarith
    have hres := pairOp_le_of_strictTouchFromBelow (C := C) (e := e) (Cstar := Cstar)
      (w := w) (g := g) (s := s) (c := c) (B := B) hs hc he0 hCsym hCk heB hB2 hCtend
      hetend hw2 heq hconv (ψ := ψδ) hψδ2 hx₀ hBψδ htouchδ
    have hhess : hessOp ψδ x₀ = hessOp ψ x₀ + (-(2 * δ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
      have hψat : ContDiffAt ℝ 2 ψ x₀ := hψ.contDiffAt (hs.mem_nhds hx₀)
      have hpat : ContDiffAt ℝ 2 (parab (2 * δ) x₀ 0) x₀ :=
        ((contDiff_parab (2 * δ) 0 x₀).contDiffAt).of_le (m := 2)
          (WithTop.coe_le_coe.mpr le_top)
      rw [show ψδ = fun y => ψ y + parab (2 * δ) x₀ 0 y from hψδdef]
      rw [hessOp_add hψat hpat, hessOp_parab]
    rw [hhess] at hres
    rw [pairOp_add, pairOp_smul, pairOp_one] at hres
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases le_or_gt (trOp Cstar) 0 with hT | hT
  · have h := hmain 1 (by norm_num) (by norm_num)
    nlinarith
  · have hpos : 0 < ε / (4 * trOp Cstar) := by positivity
    have hδpos : 0 < min 1 (ε / (4 * trOp Cstar)) := lt_min (by norm_num) hpos
    have hδle1 : min 1 (ε / (4 * trOp Cstar)) ≤ 1 := min_le_left _ _
    have h := hmain (min 1 (ε / (4 * trOp Cstar))) hδpos hδle1
    have hle : min 1 (ε / (4 * trOp Cstar)) ≤ ε / (4 * trOp Cstar) :=
      min_le_right _ _
    have h2 : min 1 (ε / (4 * trOp Cstar)) * (4 * trOp Cstar) ≤ ε := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * trOp Cstar)] at hle
      linarith
    nlinarith [h, h2, hT]

/-- **A strict maximum is propagated to the approximating family.**

Let `w k ∈ C²(s)` converge locally uniformly to `g` on the open set `s`, and suppose that `g` has a
STRICT maximum at `x₀` (in the sense that `g y < g x₀` for `y ∈ s`, `y ≠ x₀`, near `x₀`).  Then
there is a ball `closedBall x₀ R ⊆ s` and points `xk k ∈ closedBall x₀ R` with `xk k → x₀` such
that, for all large `k`, `xk k` is a local maximum of `w k`.

This is the common core of the two viscosity-stability lemmas: it converts a strict touching
condition at `x₀` into interior critical points of the approximants. -/
theorem exists_localMax_of_strictMax
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x₀ : ℝ⁴}
    (hs : IsOpen s) (hx₀ : x₀ ∈ s)
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, y ≠ x₀ → g y < g x₀) :
    ∃ R > 0, closedBall x₀ R ⊆ s ∧ ∃ xk : ℕ → ℝ⁴,
      (∀ k, xk k ∈ closedBall x₀ R) ∧ Tendsto xk atTop (𝓝 x₀) ∧
      ∀ᶠ k in atTop, IsLocalMax (w k) (xk k) := by
  classical
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := mem_nhdsWithin_iff.mp htouch
  set R : ℝ := min (ε₀ / 2) (ρ₁ / 2) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (by linarith)
  have hRε : R < ε₀ := by rw [hRdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRρ : R < ρ₁ := by rw [hRdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hRs : closedBall x₀ R ⊆ s := fun y hy => hε₀sub (by
    rw [mem_ball]
    have h := mem_closedBall.mp hy
    have h2 : dist y x₀ ≤ R := by have h3 := dist_comm x₀ y; linarith
    linarith)
  have hstrict : ∀ y ∈ closedBall x₀ R, y ≠ x₀ → g y < g x₀ := by
    intro y hy hyne
    refine hρ₁sub ⟨?_, hRs hy⟩ hyne
    rw [mem_ball]
    have h := mem_closedBall.mp hy
    have h2 : dist y x₀ ≤ R := by have h3 := dist_comm x₀ y; linarith
    linarith
  have hK : IsCompact (closedBall x₀ R) := isCompact_closedBall x₀ R
  have hconvK := hconv _ hRs hK
  have hgc : ContinuousOn g (closedBall x₀ R) :=
    hconvK.continuousOn (Filter.Frequently.of_forall fun k => ((hw2 k).continuousOn).mono hRs)
  have hcont : ∀ k, ContinuousOn (w k) (closedBall x₀ R) := fun k =>
    ((hw2 k).continuousOn).mono hRs
  choose xk hxkmem hxkmax using fun k =>
    hK.exists_isMaxOn ⟨x₀, mem_closedBall_self hRpos.le⟩ (hcont k)
  have hxkmax' : ∀ k, ∀ y ∈ closedBall x₀ R, w k y ≤ w k (xk k) := fun k => hxkmax k
  have hxk_tend : Tendsto xk atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    rw [← Filter.eventually_atTop]
    by_contra h
    rw [Filter.not_eventually] at h
    have hfr : ∃ᶠ k in atTop, δ ≤ dist (xk k) x₀ := h.mono fun k hk => not_lt.mp hk
    have hAcomp : IsCompact (closedBall x₀ R ∩ {y : ℝ⁴ | δ ≤ dist y x₀}) :=
      hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
    obtain ⟨k₁, hk₁⟩ := hfr.exists
    obtain ⟨a, haA, hamax⟩ := hAcomp.exists_isMaxOn ⟨xk k₁, hxkmem k₁, hk₁⟩
      (hgc.mono Set.inter_subset_left)
    have ha_ne : a ≠ x₀ := by
      intro h'
      have h2 : δ ≤ dist x₀ x₀ := h' ▸ haA.2
      simp at h2
      linarith
    have hgap : g a < g x₀ := hstrict a haA.1 ha_ne
    have hamax' : ∀ y ∈ closedBall x₀ R ∩ {y : ℝ⁴ | δ ≤ dist y x₀}, g y ≤ g a := hamax
    set η : ℝ := (g x₀ - g a) / 3 with hηdef
    have hηpos : 0 < η := by rw [hηdef]; linarith
    have hev := (tendstoUniformlyOn_iff.mp hconvK) η hηpos
    obtain ⟨k₂, hk₂⟩ := (hfr.and_eventually hev).exists
    have h1 : g (xk k₂) ≤ g a := hamax' _ ⟨hxkmem k₂, hk₂.1⟩
    have h2 : w k₂ (xk k₂) ≤ g (xk k₂) + η := by
      have h := hk₂.2 (xk k₂) (hxkmem k₂)
      rw [Real.dist_eq] at h
      have h' := (abs_lt.mp h).1
      linarith
    have h3 : w k₂ x₀ ≤ w k₂ (xk k₂) := hxkmax' k₂ x₀ (mem_closedBall_self hRpos.le)
    have h4 : g x₀ ≤ w k₂ x₀ + η := by
      have h := hk₂.2 x₀ (mem_closedBall_self hRpos.le)
      rw [Real.dist_eq] at h
      have h' := (abs_lt.mp h).2
      linarith
    have h5 : g x₀ ≤ g a + 2 * η := by linarith
    rw [hηdef] at h5
    linarith
  refine ⟨R, hRpos, hRs, xk, hxkmem, hxk_tend, ?_⟩
  have hxk_int : ∀ᶠ k in atTop, xk k ∈ ball x₀ R :=
    hxk_tend.eventually (isOpen_ball.mem_nhds (mem_ball_self hRpos))
  filter_upwards [hxk_int] with k hk
  rw [IsLocalMax, IsMaxFilter]
  filter_upwards [isOpen_ball.mem_nhds hk] with y hy
  exact hxkmax' k y (ball_subset_closedBall hy)

/-- **One-sided stability, touch from above.**

Let `w k ∈ C²(s)` be classical solutions of `Fop (C k) (e k) (D²·) = 0` with `C k = cofOp (N k)`,
`s2 (N k) = 1`, `trOp (N k) > 0`, `C k ⪰ c > 0`, `e k > 0`, `e k → 0`, `C k → Cstar`, converging
locally uniformly to `g`.  If a `C²` test function `ψ` touches `g` strictly from ABOVE at `x₀`
(with `‖D²ψ‖ + 3 ≤ B` near `x₀`), then `tr (Cstar ∘ D²ψ(x₀)) ≥ 0`.

The proof does NOT use monotonicity at the solution's Hessian (which is unbounded a priori);
instead one applies the from-above contact bound `contact_bound_above_sigma2` of the `σ₂` equation
to `A = N k`, `M = e k • D²w k(xk k)` (valid because at a from-above contact point of the perturbed
test function `ψ + δ‖·-x₀‖²` one has `D²w k(xk k) ⪯ D²ψ(xk k) + 2δ • 1`), which bounds the
solution's Hessian, after which `Fop_mono` is legitimate. -/
theorem pairOp_ge_of_strictTouchFromAbove
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴} {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c c' B : ℝ}
    (hs : IsOpen s) (hc : 0 < c) (hc' : 0 ≤ c')
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (hCeq : ∀ k, C k = cofOp (N k))
    (he0 : ∀ k, 0 < e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hcq : ∀ k v, c * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (hcq' : ∀ k v, ⟪C k v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (heB : ∀ᶠ k in atTop, e k * ((16 * c' / c + 1) * B) ≤ c / 2)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hpos : ∀ k, ∀ x ∈ s, 0 < trOp (N k + e k • hessOp (w k) x))
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    {ψ : ℝ⁴ → ℝ} (hψ : ContDiffOn ℝ 2 ψ s) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (hBψ : ∀ x ∈ s, ‖hessOp ψ x‖ + 3 ≤ B)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, y ≠ x₀ → g y - ψ y < g x₀ - ψ x₀) :
    0 ≤ pairOp Cstar (hessOp ψ x₀) := by
  classical
  have hB0 : 0 ≤ B := by
    have h1 := hBψ x₀ hx₀
    have h2 := norm_nonneg (hessOp ψ x₀)
    linarith
  have hmain : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      0 ≤ pairOp Cstar (hessOp ψ x₀) + 2 * δ * trOp Cstar := by
    intro δ hδpos hδ1
    set ψδ : ℝ⁴ → ℝ := fun y => ψ y + parab (-2 * δ) x₀ 0 y with hψδdef
    have hψδeq : ∀ y : ℝ⁴, ψδ y = ψ y + δ * ‖y - x₀‖ ^ 2 := by
      intro y
      simp only [hψδdef, parab_apply]
      ring
    have hψδ2 : ContDiffOn ℝ 2 ψδ s := by
      rw [show ψδ = fun y : ℝ⁴ => ψ y + parab (-2 * δ) x₀ 0 y from hψδdef]
      exact hψ.add (((contDiff_parab (-2 * δ) 0 x₀).contDiffOn).of_le (m := 2)
        (WithTop.coe_le_coe.mpr le_top))
    have hhessδ : ∀ x ∈ s, hessOp ψδ x = hessOp ψ x + (2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
      intro x hx
      have hψat : ContDiffAt ℝ 2 ψ x := hψ.contDiffAt (hs.mem_nhds hx)
      have hpat : ContDiffAt ℝ 2 (parab (-2 * δ) x₀ 0) x :=
        ((contDiff_parab (-2 * δ) 0 x₀).contDiffAt).of_le (m := 2)
          (WithTop.coe_le_coe.mpr le_top)
      have h1 : hessOp (fun y : ℝ⁴ => ψ y + parab (-2 * δ) x₀ 0 y) x
          = hessOp ψ x + hessOp (parab (-2 * δ) x₀ 0) x := hessOp_add hψat hpat
      have h2 : hessOp (parab (-2 * δ) x₀ 0) x = (2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
        rw [hessOp_parab]
        congr 1
        ring
      rw [show ψδ = fun y : ℝ⁴ => ψ y + parab (-2 * δ) x₀ 0 y from hψδdef, h1, h2]
    have hBψδ : ∀ x ∈ s, ‖hessOp ψδ x‖ ≤ B := by
      intro x hx
      rw [hhessδ x hx]
      have h1 : ‖hessOp ψ x‖ + 3 ≤ B := hBψ x hx
      have h2 : ‖(2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖ = 2 * δ := by
        rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one,
          abs_of_pos (by linarith : (0 : ℝ) < 2 * δ)]
      calc ‖hessOp ψ x + (2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖
          ≤ ‖hessOp ψ x‖ + ‖(2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖ := norm_add_le _ _
        _ = ‖hessOp ψ x‖ + 2 * δ := by rw [h2]
        _ ≤ B := by linarith
    have htouchδ : ∀ᶠ y in 𝓝[s] x₀,
        y ≠ x₀ → (fun z => g z - ψδ z) y < (fun z => g z - ψδ z) x₀ := by
      filter_upwards [htouch] with y hy hyne
      have h1 : ψδ x₀ = ψ x₀ := by rw [hψδeq]; simp
      have h2 : g y - ψδ y = (g y - ψ y) - δ * ‖y - x₀‖ ^ 2 := by rw [hψδeq y]; ring
      have h3 : 0 < δ * ‖y - x₀‖ ^ 2 := by
        have h4 : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
        positivity
      rw [h1, h2]
      linarith [hy hyne]
    have hconvW : ∀ K, K ⊆ s → IsCompact K →
        TendstoUniformlyOn (fun k => fun y : ℝ⁴ => w k y - ψδ y)
          (fun y : ℝ⁴ => g y - ψδ y) atTop K := by
      intro K hKsub hKcomp
      have h0 := hconv K hKsub hKcomp
      rw [tendstoUniformlyOn_iff] at h0 ⊢
      intro ε hε
      filter_upwards [h0 ε hε] with k hk
      intro x hx
      have h1 := hk x hx
      rw [Real.dist_eq] at h1 ⊢
      have h2 : (g x - ψδ x) - (w k x - ψδ x) = g x - w k x := by ring
      rwa [h2]
    obtain ⟨R, hRpos, hRs, xk, hxkmem, hxk_tend, hmax⟩ :=
      exists_localMax_of_strictMax hs hx₀ (fun k => (hw2 k).sub hψδ2) hconvW htouchδ
    have hfle : ∀ᶠ k in atTop, 0 ≤ Fop (C k) (e k) (hessOp ψδ (xk k)) := by
      filter_upwards [hmax, heB] with k hmaxk hBk
      have hak : xk k ∈ s := hRs (hxkmem k)
      have hwk : ContDiffAt ℝ 2 (w k) (xk k) := (hw2 k).contDiffAt (hs.mem_nhds hak)
      have hψk : ContDiffAt ℝ 2 ψδ (xk k) := hψδ2.contDiffAt (hs.mem_nhds hak)
      -- the quadratic-form comparison at the local maximum
      have hq : ∀ v : ℝ⁴, ⟪(hessOp (w k) (xk k) - hessOp ψδ (xk k)) v, v⟫ ≤ 0 := by
        intro v
        have h1 : (fderiv ℝ (fderiv ℝ (fun y => w k y - ψδ y)) (xk k)) v v ≤ 0 :=
          Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax
            (hwk.sub hψk) hmaxk v
        have h2 : (fderiv ℝ (fderiv ℝ (fun y => w k y - ψδ y)) (xk k)) v v
            = ⟪hessOp (fun y => w k y - ψδ y) (xk k) v, v⟫ := by
          rw [show hessOp (fun y => w k y - ψδ y) (xk k)
              = InnerProductSpace.continuousLinearMapOfBilin
                  (fderiv ℝ (fderiv ℝ (fun y => w k y - ψδ y)) (xk k)) from rfl]
          exact (InnerProductSpace.continuousLinearMapOfBilin_apply _ v v).symm
        have h3 : hessOp (fun y => w k y - ψδ y) (xk k)
            = hessOp (w k) (xk k) - hessOp ψδ (xk k) := hessOp_sub_of_contDiffAt hwk hψk
        rw [h2, h3] at h1
        exact h1
      -- the two-sided bound from the from-above contact bound
      have hTsym : (hessOp (w k) (xk k)).IsSymmetric := hessOp_symm_of_contDiffAt hwk
      have hMsym : (e k • hessOp (w k) (xk k)).IsSymmetric := hTsym.smul (by simp)
      have hAM1 : s2 (N k + e k • hessOp (w k) (xk k)) = 1 := by
        have hF : pairOp (cofOp (N k)) (hessOp (w k) (xk k))
            + e k * s2 (hessOp (w k) (xk k)) = 0 := by
          have h := heq k (xk k) hak
          rw [hCeq k] at h
          exact h
        have h3 := s2_add_expansion (hN k) hMsym
        rw [h3, s2_smul, hN1 k, pairOp_smul]
        have h4 : e k * (pairOp (cofOp (N k)) (hessOp (w k) (xk k))
            + e k * s2 (hessOp (w k) (xk k))) = 0 := by rw [hF, mul_zero]
        nlinarith [h4]
      have hTup : ∀ v : ℝ⁴, ⟪hessOp (w k) (xk k) v, v⟫ ≤ B * ‖v‖ ^ 2 := by
        intro v
        have hb : ‖hessOp ψδ (xk k)‖ ≤ B := hBψδ (xk k) hak
        have h1 : ⟪hessOp ψδ (xk k) v, v⟫ ≤ B * ‖v‖ ^ 2 := by
          calc ⟪hessOp ψδ (xk k) v, v⟫ ≤ |⟪hessOp ψδ (xk k) v, v⟫| := le_abs_self _
            _ ≤ ‖hessOp ψδ (xk k) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
            _ ≤ (‖hessOp ψδ (xk k)‖ * ‖v‖) * ‖v‖ :=
                mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            _ ≤ (B * ‖v‖) * ‖v‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
                  (norm_nonneg _)
            _ = B * ‖v‖ ^ 2 := by ring
        have h2 := hq v
        rw [sub_apply, inner_sub_left] at h2
        linarith
      have hMle : ∀ v : ℝ⁴, ⟪(e k • hessOp (w k) (xk k)) v, v⟫ ≤ (e k * B) * ‖v‖ ^ 2 := by
        intro v
        rw [smul_apply, real_inner_smul_left]
        have h1 := hTup v
        have h2 : e k * ⟪hessOp (w k) (xk k) v, v⟫ ≤ e k * (B * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (he0 k))
        linarith [h2]
      have hcont := contact_bound_above_sigma2 (A := N k) (M := e k • hessOp (w k) (xk k))
        (hN k) hMsym (hN1 k) hAM1 (htrN k) (hpos k (xk k) hak) hc
        (mul_nonneg (le_of_lt (he0 k)) hB0)
        (fun v => by rw [← hCeq k]; exact hcq k v)
        (fun v => by rw [← hCeq k]; exact hcq' k v) hMle
      have hTbound : ∀ v : ℝ⁴, -((4 * c' / c) * B) * ‖v‖ ^ 2 ≤ ⟪hessOp (w k) (xk k) v, v⟫ := by
        intro v
        have h1 := hcont v
        rw [smul_apply, real_inner_smul_left] at h1
        nlinarith [h1, he0 k, sq_nonneg ‖v‖]
      have htr : -((16 * c' / c) * B) ≤ trOp (hessOp (w k) (xk k)) := by
        rw [trOp_eq_sum]
        have h1 : ∀ i : Fin 4, -((4 * c' / c) * B) ≤ ⟪hessOp (w k) (xk k) (stdB4 i), stdB4 i⟫ := by
          intro i
          have h2 := hTbound (stdB4 i)
          rw [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h2
          exact h2
        have h3 : (∑ _i : Fin 4, -((4 * c' / c) * B))
            ≤ ∑ i : Fin 4, ⟪hessOp (w k) (xk k) (stdB4 i), stdB4 i⟫ :=
          Finset.sum_le_sum fun i _ => h1 i
        have h4 : (∑ _i : Fin 4, -((4 * c' / c) * B)) = -((16 * c' / c) * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring_nf
        linarith [h3, h4.le, h4.ge]
      have hcof : ∀ v : ℝ⁴, -((16 * c' / c + 1) * B) * ‖v‖ ^ 2
          ≤ ⟪cofOp (hessOp (w k) (xk k)) v, v⟫ := by
        intro v
        have h1 : cofOp (hessOp (w k) (xk k))
            = trOp (hessOp (w k) (xk k)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - hessOp (w k) (xk k) := rfl
        have h2 : ⟪cofOp (hessOp (w k) (xk k)) v, v⟫
            = trOp (hessOp (w k) (xk k)) * ‖v‖ ^ 2 - ⟪hessOp (w k) (xk k) v, v⟫ := by
          rw [h1, sub_apply, inner_sub_left, smul_apply, ContinuousLinearMap.one_apply,
            real_inner_smul_left, real_inner_self_eq_norm_sq]
        rw [h2]
        have h3 := hTup v
        nlinarith [htr, h3, sq_nonneg ‖v‖]
      have hCT : ∀ v : ℝ⁴, 0 ≤ ⟪(C k + e k • cofOp (hessOp (w k) (xk k))) v, v⟫ := by
        intro v
        have h1 : c * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫ := hcq k v
        have h2 := hcof v
        have h3 : e k * (-((16 * c' / c + 1) * B) * ‖v‖ ^ 2)
            ≤ e k * ⟪cofOp (hessOp (w k) (xk k)) v, v⟫ :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt (he0 k))
        have h4 : e k * ((16 * c' / c + 1) * B) * ‖v‖ ^ 2 ≤ c / 2 * ‖v‖ ^ 2 := by
          nlinarith [hBk, sq_nonneg ‖v‖]
        have h5 : ⟪(C k + e k • cofOp (hessOp (w k) (xk k))) v, v⟫
            = ⟪C k v, v⟫ + e k * ⟪cofOp (hessOp (w k) (xk k)) v, v⟫ := by
          rw [add_apply, inner_add_left, smul_apply, real_inner_smul_left]
        rw [h5]
        nlinarith [h1, h3, h4, sq_nonneg ‖v‖]
      have hST : ∀ v : ℝ⁴, 0 ≤ ⟪(hessOp ψδ (xk k) - hessOp (w k) (xk k)) v, v⟫ := by
        intro v
        have h2 := hq v
        rw [show (hessOp ψδ (xk k) - hessOp (w k) (xk k))
            = -(hessOp (w k) (xk k) - hessOp ψδ (xk k)) from by abel]
        rw [neg_apply, inner_neg_left]
        linarith
      have hmono := Fop_mono (hCsym k) (le_of_lt (he0 k)) (hessOp_symm_of_contDiffAt hψk)
        (hessOp_symm_of_contDiffAt hwk) hST hCT
      rwa [heq k (xk k) hak] at hmono
    -- pass to the limit
    have hMbound : ∀ k, ‖hessOp ψδ (xk k)‖ ≤ B := fun k => hBψδ (xk k) (hRs (hxkmem k))
    have hAcont : ContinuousAt (fun x => fderiv ℝ (fderiv ℝ ψδ) x) x₀ :=
      ((hψδ2.contDiffAt (hs.mem_nhds hx₀)).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv
        (by norm_num)
    have hAtend : Tendsto (fun k => fderiv ℝ (fderiv ℝ ψδ) (xk k)) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ ψδ) x₀)) := hAcont.tendsto.comp hxk_tend
    have heval : ∀ i j : Fin 4,
        Tendsto (fun k => fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)) atTop
          (𝓝 (fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j))) := by
      intro i j
      have hcontEval : Continuous (fun M : ℝ⁴ →L[ℝ] (ℝ⁴ →L[ℝ] ℝ) => M (stdB4 i) (stdB4 j)) :=
        ((ContinuousLinearMap.apply ℝ ℝ (stdB4 j)).continuous.comp
          (ContinuousLinearMap.apply ℝ (ℝ⁴ →L[ℝ] ℝ) (stdB4 i)).continuous)
      exact (hcontEval.tendsto (fderiv ℝ (fderiv ℝ ψδ) x₀)).comp hAtend
    have hterm : ∀ i j : Fin 4, Tendsto (fun k =>
        |fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j)|) atTop (𝓝 0) := by
      intro i j
      have h1 : Tendsto (fun _ : ℕ => fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j)) atTop
          (𝓝 (fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j))) := tendsto_const_nhds
      have h := ((heval i j).sub h1).abs
      simpa using h
    have hscl : Tendsto (fun k => ∑ i : Fin 4, ∑ j : Fin 4,
        |fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j)|) atTop (𝓝 0) := by
      have h := tendsto_finset_sum Finset.univ
        (fun i _ => tendsto_finset_sum Finset.univ (fun j _ => hterm i j))
      simpa using h
    have hCsub : Tendsto (fun k => C k - Cstar) atTop (𝓝 0) := by
      have h1 : Tendsto (fun _ : ℕ => Cstar) atTop (𝓝 Cstar) := tendsto_const_nhds
      have h := hCtend.sub h1
      simpa using h
    have hMdiff : ∀ k, ‖hessOp ψδ (xk k) - hessOp ψδ x₀‖
        ≤ ∑ i : Fin 4, ∑ j : Fin 4,
            |fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)
              - fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j)| := by
      intro k
      have h1 : hessOp ψδ (xk k) - hessOp ψδ x₀
          = InnerProductSpace.continuousLinearMapOfBilin
              (fderiv ℝ (fderiv ℝ ψδ) (xk k) - fderiv ℝ (fderiv ℝ ψδ) x₀) := by
        rw [show hessOp ψδ (xk k) = InnerProductSpace.continuousLinearMapOfBilin
              (fderiv ℝ (fderiv ℝ ψδ) (xk k)) from rfl,
            show hessOp ψδ x₀ = InnerProductSpace.continuousLinearMapOfBilin
              (fderiv ℝ (fderiv ℝ ψδ) x₀) from rfl,
            Commons.Analysis.Calculus.FDeriv.continuousLinearMapOfBilin_sub]
      rw [h1]
      refine le_trans (norm_le_sum_abs_inner _) ?_
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
      have h2 : (fderiv ℝ (fderiv ℝ ψδ) (xk k) - fderiv ℝ (fderiv ℝ ψδ) x₀)
          (stdB4 i) (stdB4 j)
          = fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)
            - fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j) := by
        simp only [sub_apply]
      rw [h2]
    have ht1 : Tendsto (fun k => pairOp (C k - Cstar) (hessOp ψδ (xk k))) atTop (𝓝 0) := by
      have ha : Tendsto (fun k => 4 * B * ‖C k - Cstar‖) atTop (𝓝 0) := by
        have h0 : Tendsto (fun k => ‖C k - Cstar‖) atTop (𝓝 0) := by simpa using hCsub.norm
        have h := h0.const_mul (4 * B)
        simpa using h
      refine squeeze_zero_norm' (a := fun k => 4 * B * ‖C k - Cstar‖) ?_ ha
      filter_upwards with k
      calc ‖pairOp (C k - Cstar) (hessOp ψδ (xk k))‖
          = |pairOp (C k - Cstar) (hessOp ψδ (xk k))| := Real.norm_eq_abs _
        _ ≤ 4 * ‖C k - Cstar‖ * ‖hessOp ψδ (xk k)‖ := abs_pairOp_le _ _
        _ ≤ 4 * ‖C k - Cstar‖ * B := mul_le_mul_of_nonneg_left (hMbound k) (by positivity)
        _ = 4 * B * ‖C k - Cstar‖ := by ring
    have ht2 : Tendsto (fun k => pairOp Cstar (hessOp ψδ (xk k) - hessOp ψδ x₀))
        atTop (𝓝 0) := by
      have ha : Tendsto (fun k => 4 * ‖Cstar‖ * (∑ i : Fin 4, ∑ j : Fin 4,
          |fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)
            - fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j)|)) atTop (𝓝 0) := by
        have h := hscl.const_mul (4 * ‖Cstar‖)
        simpa using h
      refine squeeze_zero_norm' (a := fun k => 4 * ‖Cstar‖ * (∑ i : Fin 4, ∑ j : Fin 4,
          |fderiv ℝ (fderiv ℝ ψδ) (xk k) (stdB4 i) (stdB4 j)
            - fderiv ℝ (fderiv ℝ ψδ) x₀ (stdB4 i) (stdB4 j)|)) ?_ ha
      filter_upwards with k
      calc ‖pairOp Cstar (hessOp ψδ (xk k) - hessOp ψδ x₀)‖
          = |pairOp Cstar (hessOp ψδ (xk k) - hessOp ψδ x₀)| := Real.norm_eq_abs _
        _ ≤ 4 * ‖Cstar‖ * ‖hessOp ψδ (xk k) - hessOp ψδ x₀‖ := abs_pairOp_le _ _
        _ ≤ 4 * ‖Cstar‖ * _ := mul_le_mul_of_nonneg_left (hMdiff k) (by positivity)
    have ht3 : Tendsto (fun k => e k * s2 (hessOp ψδ (xk k))) atTop (𝓝 0) := by
      have ha : Tendsto (fun k => e k * (32 * B ^ 2)) atTop (𝓝 0) := by
        have h := hetend.mul_const (32 * B ^ 2)
        simpa using h
      refine squeeze_zero_norm' (a := fun k => e k * (32 * B ^ 2)) ?_ ha
      filter_upwards with k
      have hb : ‖hessOp ψδ (xk k)‖ ≤ B := hMbound k
      have hek : 0 ≤ e k := le_of_lt (he0 k)
      calc ‖e k * s2 (hessOp ψδ (xk k))‖ = |e k * s2 (hessOp ψδ (xk k))| := Real.norm_eq_abs _
        _ = |e k| * |s2 (hessOp ψδ (xk k))| := abs_mul _ _
        _ = e k * |s2 (hessOp ψδ (xk k))| := by rw [abs_of_nonneg hek]
        _ ≤ e k * (32 * ‖hessOp ψδ (xk k)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (abs_s2_le _) hek
        _ ≤ e k * (32 * B ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hek
            nlinarith [hb, norm_nonneg (hessOp ψδ (xk k)), hB0]
    have hmix : Tendsto (fun k => pairOp (C k - Cstar) (hessOp ψδ (xk k))
        + (pairOp Cstar (hessOp ψδ (xk k) - hessOp ψδ x₀) + e k * s2 (hessOp ψδ (xk k))))
        atTop (𝓝 0) := by
      have h := ht1.add (ht2.add ht3)
      simpa using h
    have hflim : Tendsto (fun k => Fop (C k) (e k) (hessOp ψδ (xk k))) atTop
        (𝓝 (pairOp Cstar (hessOp ψδ x₀))) := by
      have hkey : (fun k => pairOp (C k - Cstar) (hessOp ψδ (xk k))
          + (pairOp Cstar (hessOp ψδ (xk k) - hessOp ψδ x₀) + e k * s2 (hessOp ψδ (xk k))))
          = fun k => Fop (C k) (e k) (hessOp ψδ (xk k)) - pairOp Cstar (hessOp ψδ x₀) := by
        funext k
        have h1 : pairOp (C k) (hessOp ψδ (xk k))
            = pairOp (C k - Cstar) (hessOp ψδ (xk k)) + pairOp Cstar (hessOp ψδ (xk k)) := by
          have he : C k = C k - Cstar + Cstar := by abel
          conv_lhs => rw [he]
          rw [pairOp_add_left]
        have h2 : pairOp Cstar (hessOp ψδ (xk k))
            = pairOp Cstar (hessOp ψδ (xk k) - hessOp ψδ x₀) + pairOp Cstar (hessOp ψδ x₀) := by
          have he : hessOp ψδ (xk k) = (hessOp ψδ (xk k) - hessOp ψδ x₀) + hessOp ψδ x₀ := by abel
          conv_lhs => rw [he]
          rw [pairOp_add]
        unfold Fop
        rw [h1, h2]
        ring
      rw [hkey] at hmix
      have h := hmix.add_const (pairOp Cstar (hessOp ψδ x₀))
      have h' : (fun k => (Fop (C k) (e k) (hessOp ψδ (xk k)) - pairOp Cstar (hessOp ψδ x₀))
          + pairOp Cstar (hessOp ψδ x₀)) = fun k => Fop (C k) (e k) (hessOp ψδ (xk k)) := by
        funext k; ring
      rw [h'] at h
      simpa using h
    have hlim : 0 ≤ pairOp Cstar (hessOp ψδ x₀) := by
      have h1 : Tendsto (fun k => -(Fop (C k) (e k) (hessOp ψδ (xk k)))) atTop
          (𝓝 (-(pairOp Cstar (hessOp ψδ x₀)))) := hflim.neg
      have h2 : ∀ᶠ k in atTop, -(Fop (C k) (e k) (hessOp ψδ (xk k))) ≤ 0 :=
        hfle.mono fun k hk => by linarith
      have h3 := le_of_tendsto h1 h2
      linarith
    have hfin : pairOp Cstar (hessOp ψδ x₀) = pairOp Cstar (hessOp ψ x₀) + 2 * δ * trOp Cstar := by
      rw [hhessδ x₀ hx₀, pairOp_add, pairOp_smul, pairOp_one]
    linarith [hlim, hfin.le, hfin.ge]
  by_contra h
  push_neg at h
  rcases le_or_gt (trOp Cstar) 0 with hT | hT
  · have h2 := hmain (1 / 2) (by norm_num) (by norm_num)
    nlinarith
  · have hTpos : 0 < 4 * trOp Cstar := by linarith
    set m : ℝ := min 1 (-(pairOp Cstar (hessOp ψ x₀)) / (4 * trOp Cstar)) with hmdef
    have hmpos : 0 < m := by
      rw [hmdef]
      refine lt_min (by norm_num) ?_
      exact div_pos (by linarith) hTpos
    have hm1 : m ≤ 1 := by rw [hmdef]; exact min_le_left _ _
    have h2 := hmain m hmpos hm1
    have h3 : m * (4 * trOp Cstar) ≤ -(pairOp Cstar (hessOp ψ x₀)) := by
      have h4 : m ≤ -(pairOp Cstar (hessOp ψ x₀)) / (4 * trOp Cstar) := by
        rw [hmdef]; exact min_le_right _ _
      rw [le_div_iff₀ hTpos] at h4
      linarith [h4]
    nlinarith [h2, h3]

/-- The Hessian operator of a `C²` function is locally bounded, with an explicit bound in terms of
the matrix entries at the centre: for `x` near `x₀`,
`‖hessOp ψ x‖ ≤ ∑ᵢⱼ |(D²ψ(x₀)) eᵢ eⱼ| + 16`. -/
theorem eventually_hessOp_le {ψ : ℝ⁴ → ℝ} {x₀ : ℝ⁴} (hψ : ContDiffAt ℝ 2 ψ x₀) :
    ∀ᶠ x in 𝓝 x₀, ‖hessOp ψ x‖
      ≤ (∑ i : Fin 4, ∑ j : Fin 4, |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) + 16 := by
  have hAcont : ContinuousAt (fun x => fderiv ℝ (fderiv ℝ ψ) x) x₀ :=
    (hψ.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  have hev : ∀ i j : Fin 4, ∀ᶠ x in 𝓝 x₀,
      |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)|
        ≤ |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| + 1 := by
    intro i j
    have hcontEval : ContinuousAt (fun M : ℝ⁴ →L[ℝ] (ℝ⁴ →L[ℝ] ℝ) => M (stdB4 i) (stdB4 j))
        (fderiv ℝ (fderiv ℝ ψ) x₀) :=
      (((ContinuousLinearMap.apply ℝ ℝ (stdB4 j)).continuous.comp
        (ContinuousLinearMap.apply ℝ (ℝ⁴ →L[ℝ] ℝ) (stdB4 i)).continuous)).continuousAt
    have h1 := hcontEval.tendsto.comp hAcont.tendsto
    have h2 : ∀ᶠ x in 𝓝 x₀, |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)
        - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| < 1 := by
      have h3 : Tendsto (fun x => |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) (𝓝 x₀) (𝓝 0) := by
        have h5 : Tendsto (fun _ : ℝ⁴ => fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j))
            (𝓝 x₀) (𝓝 (fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j))) :=
          tendsto_const_nhds
        have h6 := h1.sub h5
        simpa using h6.abs
      exact h3.eventually_lt_const (by norm_num)
    filter_upwards [h2] with x hx
    have h8 : |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)|
        - |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|
        ≤ |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)
          - fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| :=
      abs_sub_abs_le_abs_sub _ _
    linarith [(abs_lt.mp hx).2, h8]
  have hev' : ∀ᶠ x in 𝓝 x₀, ∀ i j : Fin 4,
      |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)|
        ≤ |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| + 1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    exact hev i
  filter_upwards [hev'] with x hx
  calc ‖hessOp ψ x‖ ≤ ∑ i : Fin 4, ∑ j : Fin 4,
        |fderiv ℝ (fderiv ℝ ψ) x (stdB4 i) (stdB4 j)| := by
        rw [show hessOp ψ x = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ ψ) x) from rfl]
        refine le_trans (norm_le_sum_abs_inner _) ?_
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4,
        (|fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| + 1) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hx i j
    _ = (∑ i : Fin 4, ∑ j : Fin 4, |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) + 16 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num

/-- **One-sided stability from below, with a locally derived ellipticity bound on the test
function.**  Same as `pairOp_le_of_touchFromBelow`, but the constant `B` and the smallness
hypothesis `5 B e k ≤ c/2` are NOT assumed: they are derived from the continuity of
`x ↦ hessOp ψ x` at `x₀` and from `e k → 0`.  This is the form needed for the viscosity limit. -/
theorem pairOp_le_of_touchFromBelow_loc
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c : ℝ}
    (hs : IsOpen s) (hc : 0 < c)
    (he0 : ∀ k, 0 ≤ e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hCk : ∀ k v, c / 2 * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    {ψ : ℝ⁴ → ℝ} (hψ : ContDiffOn ℝ 2 ψ s) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, g x₀ - ψ x₀ ≤ g y - ψ y) :
    pairOp Cstar (hessOp ψ x₀) ≤ 0 := by
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  obtain ⟨ρ, hρpos, hρb⟩ : ∃ ρ > 0, ∀ x : ℝ⁴, dist x x₀ < ρ →
      ‖hessOp ψ x‖
        ≤ (∑ i : Fin 4, ∑ j : Fin 4, |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) + 16 :=
    Metric.eventually_nhds_iff.mp (eventually_hessOp_le (hψ.contDiffAt (hs.mem_nhds hx₀)))
  set M : ℝ := ∑ i : Fin 4, ∑ j : Fin 4,
    |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set B : ℝ := M + 24 with hBdef
  set R : ℝ := min (min (ε₀ / 2) (ρ / 2)) 1 with hRdef
  have hRpos : 0 < R := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hRε : R ≤ ε₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRρ : R ≤ ρ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRsub : ball x₀ R ⊆ s := fun y hy => hε₀sub (by
    rw [mem_ball] at hy ⊢
    linarith)
  have hRb : ∀ x ∈ ball x₀ R, ‖hessOp ψ x‖ ≤ M + 16 := by
    intro x hx
    have h1 := hρb x (by rw [mem_ball] at hx; linarith [hx, hRρ])
    rw [hMdef]; exact h1
  have hBψ : ∀ x ∈ ball x₀ R, ‖hessOp ψ x‖ + 5 ≤ B := by
    intro x hx
    have h := hRb x hx
    rw [hBdef]
    linarith
  have heB : ∀ᶠ k in atTop, 5 * B * e k ≤ c / 2 := by
    have h0 : Tendsto (fun k => 5 * B * e k) atTop (𝓝 0) := by
      have h := hetend.const_mul (5 * B)
      simpa using h
    exact (h0.eventually_lt_const (by linarith : (0 : ℝ) < c / 2)).mono fun k hk => le_of_lt hk
  have hB2 : 2 ≤ B := by rw [hBdef]; linarith
  have htouch' : ∀ᶠ y in 𝓝[ball x₀ R] x₀, g x₀ - ψ x₀ ≤ g y - ψ y :=
    nhdsWithin_mono x₀ hRsub htouch
  exact pairOp_le_of_touchFromBelow (C := C) (e := e) (Cstar := Cstar) (w := w) (g := g)
    (s := ball x₀ R) (c := c) (B := B) isOpen_ball hc he0 hCsym hCk heB hB2
    hCtend hetend (fun k => (hw2 k).mono hRsub)
    (fun k x hx => heq k x (hRsub hx))
    (fun K hK hKc => hconv K (fun z hz => hRsub (hK hz)) hKc)
    (hψ.mono hRsub) (mem_ball_self hRpos) hBψ htouch'

/-- **One-sided stability from above (non-strict touching).**  Obtained from the strict version by
the perturbation `ψ + δ‖·-x₀‖²` and `δ → 0⁺`. -/
theorem pairOp_ge_of_touchFromAbove
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴} {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c c' B : ℝ}
    (hs : IsOpen s) (hc : 0 < c) (hc' : 0 ≤ c')
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (hCeq : ∀ k, C k = cofOp (N k))
    (he0 : ∀ k, 0 < e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hcq : ∀ k v, c * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (hcq' : ∀ k v, ⟪C k v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (heB : ∀ᶠ k in atTop, e k * ((16 * c' / c + 1) * B) ≤ c / 2)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hpos : ∀ k, ∀ x ∈ s, 0 < trOp (N k + e k • hessOp (w k) x))
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    {ψ : ℝ⁴ → ℝ} (hψ : ContDiffOn ℝ 2 ψ s) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (hBψ : ∀ x ∈ s, ‖hessOp ψ x‖ + 5 ≤ B)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, y ≠ x₀ → g y - ψ y ≤ g x₀ - ψ x₀) :
    0 ≤ pairOp Cstar (hessOp ψ x₀) := by
  classical
  have hmain : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      0 ≤ pairOp Cstar (hessOp ψ x₀) + 2 * δ * trOp Cstar := by
    intro δ hδpos hδ1
    set ψδ : ℝ⁴ → ℝ := fun y => ψ y + parab (-2 * δ) x₀ 0 y with hψδdef
    have hψδeq : ∀ y : ℝ⁴, ψδ y = ψ y + δ * ‖y - x₀‖ ^ 2 := by
      intro y
      simp only [hψδdef, parab_apply]
      ring
    have hψδ2 : ContDiffOn ℝ 2 ψδ s := by
      rw [show ψδ = fun y : ℝ⁴ => ψ y + parab (-2 * δ) x₀ 0 y from hψδdef]
      exact hψ.add (((contDiff_parab (-2 * δ) 0 x₀).contDiffOn).of_le (m := 2)
        (WithTop.coe_le_coe.mpr le_top))
    have hhessδ : ∀ x ∈ s, hessOp ψδ x = hessOp ψ x + (2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
      intro x hx
      have hψat : ContDiffAt ℝ 2 ψ x := hψ.contDiffAt (hs.mem_nhds hx)
      have hpat : ContDiffAt ℝ 2 (parab (-2 * δ) x₀ 0) x :=
        ((contDiff_parab (-2 * δ) 0 x₀).contDiffAt).of_le (m := 2)
          (WithTop.coe_le_coe.mpr le_top)
      have h1 : hessOp (fun y : ℝ⁴ => ψ y + parab (-2 * δ) x₀ 0 y) x
          = hessOp ψ x + hessOp (parab (-2 * δ) x₀ 0) x := hessOp_add hψat hpat
      have h2 : hessOp (parab (-2 * δ) x₀ 0) x = (2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
        rw [hessOp_parab]
        congr 1
        ring
      rw [show ψδ = fun y : ℝ⁴ => ψ y + parab (-2 * δ) x₀ 0 y from hψδdef, h1, h2]
    have hBψδ : ∀ x ∈ s, ‖hessOp ψδ x‖ + 3 ≤ B := by
      intro x hx
      rw [hhessδ x hx]
      have h1 : ‖hessOp ψ x‖ + 5 ≤ B := hBψ x hx
      have h2 : ‖(2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖ = 2 * δ := by
        rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one,
          abs_of_pos (by linarith : (0 : ℝ) < 2 * δ)]
      have h3 := norm_add_le (hessOp ψ x) ((2 * δ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))
      rw [h2] at h3
      linarith
    have htouchδ : ∀ᶠ y in 𝓝[s] x₀,
        y ≠ x₀ → (fun z => g z - ψδ z) y < (fun z => g z - ψδ z) x₀ := by
      filter_upwards [htouch] with y hy hyne
      have h1 : ψδ x₀ = ψ x₀ := by rw [hψδeq]; simp
      have h2 : g y - ψδ y = (g y - ψ y) - δ * ‖y - x₀‖ ^ 2 := by rw [hψδeq y]; ring
      have h3 : 0 < δ * ‖y - x₀‖ ^ 2 := by
        have h4 : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
        positivity
      rw [h1, h2]
      linarith [hy hyne]
    have hres := pairOp_ge_of_strictTouchFromAbove (C := C) (e := e) (Cstar := Cstar)
      (N := N) (w := w) (g := g) (s := s) (c := c) (c' := c') (B := B) hs hc hc' hN hN1
      htrN hCeq he0 hCsym hcq hcq' heB hCtend hetend hw2 heq hpos hconv
      (ψ := ψδ) hψδ2 hx₀ hBψδ htouchδ
    have hfin : pairOp Cstar (hessOp ψδ x₀)
        = pairOp Cstar (hessOp ψ x₀) + 2 * δ * trOp Cstar := by
      rw [hhessδ x₀ hx₀, pairOp_add, pairOp_smul, pairOp_one]
    linarith [hres, hfin.le, hfin.ge]
  by_contra h
  push_neg at h
  rcases le_or_gt (trOp Cstar) 0 with hT | hT
  · have h2 := hmain (1 / 2) (by norm_num) (by norm_num)
    nlinarith
  · have hTpos : 0 < 4 * trOp Cstar := by linarith
    set m : ℝ := min 1 (-(pairOp Cstar (hessOp ψ x₀)) / (4 * trOp Cstar)) with hmdef
    have hmpos : 0 < m := by
      rw [hmdef]
      exact lt_min (by norm_num) (div_pos (by linarith) hTpos)
    have hm1 : m ≤ 1 := by rw [hmdef]; exact min_le_left _ _
    have h2 := hmain m hmpos hm1
    have h3 : m * (4 * trOp Cstar) ≤ -(pairOp Cstar (hessOp ψ x₀)) := by
      have h4 : m ≤ -(pairOp Cstar (hessOp ψ x₀)) / (4 * trOp Cstar) := by
        rw [hmdef]; exact min_le_right _ _
      rw [le_div_iff₀ hTpos] at h4
      linarith [h4]
    nlinarith [h2, h3]

/-- **One-sided stability from above, with a locally derived ellipticity bound.**  The analogue of
`pairOp_le_of_touchFromBelow_loc`. -/
theorem pairOp_ge_of_touchFromAbove_loc
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴} {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c c' : ℝ}
    (hs : IsOpen s) (hc : 0 < c) (hc' : 0 ≤ c')
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (hCeq : ∀ k, C k = cofOp (N k))
    (he0 : ∀ k, 0 < e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hcq : ∀ k v, c * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (hcq' : ∀ k v, ⟪C k v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hpos : ∀ k, ∀ x ∈ s, 0 < trOp (N k + e k • hessOp (w k) x))
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K)
    {ψ : ℝ⁴ → ℝ} (hψ : ContDiffOn ℝ 2 ψ s) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (htouch : ∀ᶠ y in 𝓝[s] x₀, y ≠ x₀ → g y - ψ y ≤ g x₀ - ψ x₀) :
    0 ≤ pairOp Cstar (hessOp ψ x₀) := by
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  obtain ⟨ρ, hρpos, hρb⟩ : ∃ ρ > 0, ∀ x : ℝ⁴, dist x x₀ < ρ →
      ‖hessOp ψ x‖
        ≤ (∑ i : Fin 4, ∑ j : Fin 4, |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)|) + 16 :=
    Metric.eventually_nhds_iff.mp (eventually_hessOp_le (hψ.contDiffAt (hs.mem_nhds hx₀)))
  set M : ℝ := ∑ i : Fin 4, ∑ j : Fin 4,
    |fderiv ℝ (fderiv ℝ ψ) x₀ (stdB4 i) (stdB4 j)| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set B : ℝ := M + 24 with hBdef
  set R : ℝ := min (min (ε₀ / 2) (ρ / 2)) 1 with hRdef
  have hRpos : 0 < R := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hRε : R ≤ ε₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRρ : R ≤ ρ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRsub : ball x₀ R ⊆ s := fun y hy => hε₀sub (by
    rw [mem_ball] at hy ⊢
    linarith)
  have hRb : ∀ x ∈ ball x₀ R, ‖hessOp ψ x‖ ≤ M + 16 := by
    intro x hx
    have h1 := hρb x (by rw [mem_ball] at hx; linarith [hx, hRρ])
    rw [hMdef]; exact h1
  have hBψ : ∀ x ∈ ball x₀ R, ‖hessOp ψ x‖ + 5 ≤ B := by
    intro x hx
    have h := hRb x hx
    rw [hBdef]
    linarith
  have heB : ∀ᶠ k in atTop, e k * ((16 * c' / c + 1) * B) ≤ c / 2 := by
    have h0 : Tendsto (fun k => e k * ((16 * c' / c + 1) * B)) atTop (𝓝 0) := by
      have h := hetend.mul_const ((16 * c' / c + 1) * B)
      simpa using h
    exact (h0.eventually_lt_const (by linarith : (0 : ℝ) < c / 2)).mono fun k hk => le_of_lt hk
  have htouch' : ∀ᶠ y in 𝓝[ball x₀ R] x₀, y ≠ x₀ → g y - ψ y ≤ g x₀ - ψ x₀ :=
    nhdsWithin_mono x₀ hRsub htouch
  exact pairOp_ge_of_touchFromAbove (C := C) (e := e) (Cstar := Cstar) (N := N)
    (w := w) (g := g) (s := ball x₀ R) (c := c) (c' := c') (B := B) isOpen_ball hc hc'
    hN hN1 htrN hCeq he0 hCsym hcq hcq' heB hCtend hetend (fun k => (hw2 k).mono hRsub)
    (fun k x hx => heq k x (hRsub hx)) (fun k x hx => hpos k x (hRsub hx))
    (fun K hK hKc => hconv K (fun z hz => hRsub (hK hz)) hKc)
    (hψ.mono hRsub) (mem_ball_self hRpos) hBψ htouch'

/-- **The viscosity limit of the small-perturbation equation.**

Let `w k ∈ C²(s)` be classical solutions of `Fop (C k) (e k) (D²·) = 0` on the open set `s`, where
`C k = cofOp (N k)` with `s2 (N k) = 1`, `trOp (N k) > 0`, `cofOp (N k)` bounded between `c > 0` and
`c'`, where `0 < e k → 0`, `C k → Cstar` and `w k → g` locally uniformly on `s`.  Then `g` is a
viscosity solution of the linearised (proper) equation `-tr (Cstar ∘ D²·) = 0` on `s`.

The two one-sided halves are `pairOp_le_of_touchFromBelow_loc` (touches from below) and
`pairOp_ge_of_touchFromAbove_loc` (touches from above, which uses the from-above contact bound of
the `σ₂` equation to control the solution's Hessian). -/
theorem isViscSolution_limit
    {C : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {Cstar : ℝ⁴ →L[ℝ] ℝ⁴} {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴}
    {w : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {c c' : ℝ}
    (hs : IsOpen s) (hc : 0 < c) (hc' : 0 ≤ c')
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (hCeq : ∀ k, C k = cofOp (N k))
    (he0 : ∀ k, 0 < e k) (hCsym : ∀ k, (C k).IsSymmetric)
    (hcq : ∀ k v, c * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫)
    (hcq' : ∀ k v, ⟪C k v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hCtend : Tendsto C atTop (𝓝 Cstar)) (hetend : Tendsto e atTop (𝓝 0))
    (hw2 : ∀ k, ContDiffOn ℝ 2 (w k) s)
    (heq : ∀ k, ∀ x ∈ s, Fop (C k) (e k) (hessOp (w k) x) = 0)
    (hpos : ∀ k, ∀ x ∈ s, 0 < trOp (N k + e k • hessOp (w k) x))
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn w g atTop K) :
    IsViscSolution (fun M => -pairOp Cstar M) g s := by
  constructor
  · -- touches from above: the subsolution half
    intro φ hφ x₀ hx₀ hmax
    have h1 : 0 ≤ pairOp Cstar (hessOp φ x₀) :=
      pairOp_ge_of_touchFromAbove_loc hs hc hc' hN hN1 htrN hCeq he0 hCsym hcq hcq' hCtend
        hetend hw2 heq hpos hconv hφ hx₀ (by
          filter_upwards [hmax] with y hy hyne
          exact hy)
    have h2 : HessOp φ s x₀ = hessOp φ x₀ :=
      Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian (hs.mem_nhds hx₀)
    rw [h2]
    linarith
  · -- touches from below: the supersolution half
    intro φ hφ x₀ hx₀ hmin
    have hCk2 : ∀ k v, c / 2 * ‖v‖ ^ 2 ≤ ⟪C k v, v⟫ := fun k v =>
      le_trans (by nlinarith [sq_nonneg ‖v‖, hc]) (hcq k v)
    have h1 : pairOp Cstar (hessOp φ x₀) ≤ 0 :=
      pairOp_le_of_touchFromBelow_loc hs hc (fun k => (he0 k).le) hCsym hCk2 hCtend hetend hw2
        heq hconv hφ hx₀
        (by
          filter_upwards [hmin] with y hy
          exact hy)
    have h2 : HessOp φ s x₀ = hessOp φ x₀ :=
      Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian (hs.mem_nhds hx₀)
    rw [h2]
    linarith

/-- The `ε`-form of the equation is equivalent to the `s2`-form: for symmetric `N`, `M` with
`s2 N = 1` and `ε ≠ 0`, `Fop (cofOp N) ε M = 0` iff `s2 (N + ε • M) = 1`. -/
theorem fop_eq_zero_iff_s2 {N M : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) (hM : M.IsSymmetric)
    {ε : ℝ} (hε : ε ≠ 0) (hN1 : s2 N = 1) :
    Fop (cofOp N) ε M = 0 ↔ s2 (N + ε • M) = 1 := by
  have hMsym : (ε • M).IsSymmetric := hM.smul (by simp)
  have hkey : s2 (N + ε • M) = 1 + ε * Fop (cofOp N) ε M := by
    rw [s2_add_expansion hN hMsym, s2_smul, pairOp_smul, Fop, hN1]
    ring
  rw [hkey]
  constructor
  · intro h
    rw [h, mul_zero, add_zero]
  · intro h
    have h1 : ε * Fop (cofOp N) ε M = 0 := by linarith [h]
    exact (mul_eq_zero.mp h1).resolve_left hε

end

end Submission
