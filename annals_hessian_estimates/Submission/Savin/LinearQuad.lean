/-
# The linear theory of Savin's Proposition 4.1: quadratic approximation

The limit of the rescaled functions `w_r(x) = Φ(rx)/r^{2+β}` (as `r → 0`) is a viscosity
solution of the constant-coefficient linear equation `tr (cofOp N ∘ D²w) = 0`.  Substituting a
symmetric square root `B` of `cofOp N` turns it into the Laplace equation for `y ↦ w (B y)`
(`Submission.Savin.LinearTheory.mvp_of_visc_linear`), which therefore has the ball mean value
property, is smooth and harmonic (`Commons.Analysis.Harmonic.mvp_contDiff_harmonic`), and is
approximated by a harmonic quadratic polynomial
(`Commons.Analysis.Harmonic.quadratic_approx_of_harmonic_lt_one`).

This file transfers that approximation back to `w`: the main result is
`Submission.linear_quadratic_approx`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Spec
import Submission.Savin.LinearTheory
import Submission.Savin.Operator
import Submission.Savin.Diag
import Submission.Commons.Analysis.Harmonic.mvp_contDiff_harmonic
import Submission.Commons.Analysis.Harmonic.quadratic_approx_of_harmonic_lt_one
import Submission.Commons.Analysis.Harmonic.quadratic_approx_of_harmonic_uniform
import Submission.Commons.Measure.Lebesgue.setAverage_comp_smul_ball
import Submission.Commons.Measure.Average.setAverage_ball_comp_smul_sub
import Submission.Commons.Topology.Metric.dist_add_le_of_closedBall_subset

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-! ## Norms from quadratic-form bounds -/

/-- For a symmetric operator `B`, `‖B u‖ ^ 2 = ⟪(B ∘ B) u, u⟫`. -/
theorem norm_sq_eq_pair_self {B : ℝ⁴ →L[ℝ] ℝ⁴} (hB : B.IsSymmetric) (u : ℝ⁴) :
    ‖B u‖ ^ 2 = ⟪(B * B) u, u⟫ := by
  have h1 : (B * B) u = B (B u) := ContinuousLinearMap.mul_apply B B u
  rw [h1, ← real_inner_self_eq_norm_sq]
  exact (hB (B u) u).symm

/-- An upper quadratic-form bound gives an upper norm bound. -/
theorem norm_le_sqrt_mul {B : ℝ⁴ →L[ℝ] ℝ⁴} (hB : B.IsSymmetric) {c' : ℝ} (hc' : 0 ≤ c')
    (h : ∀ u : ℝ⁴, ⟪(B * B) u, u⟫ ≤ c' * ‖u‖ ^ 2) (u : ℝ⁴) :
    ‖B u‖ ≤ Real.sqrt c' * ‖u‖ := by
  have h2 : ‖B u‖ ^ 2 ≤ (Real.sqrt c' * ‖u‖) ^ 2 := by
    rw [norm_sq_eq_pair_self hB, mul_pow, Real.sq_sqrt hc']
    exact h u
  calc ‖B u‖ = Real.sqrt (‖B u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt c' * ‖u‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt c' * ‖u‖ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-- A lower quadratic-form bound gives an upper bound for the inverse. -/
theorem norm_inverse_le {B : ℝ⁴ →L[ℝ] ℝ⁴} (hB : B.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (h : ∀ u : ℝ⁴, c * ‖u‖ ^ 2 ≤ ⟪(B * B) u, u⟫) (hBi : B * B.inverse = 1) (x : ℝ⁴) :
    ‖B.inverse x‖ ≤ ‖x‖ / Real.sqrt c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hx : B (B.inverse x) = x := by
    have h1 : (B * B.inverse) x = x := by rw [hBi]; rfl
    rwa [ContinuousLinearMap.mul_apply] at h1
  have h1 : c * ‖B.inverse x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc c * ‖B.inverse x‖ ^ 2 ≤ ⟪(B * B) (B.inverse x), B.inverse x⟫ := h _
      _ = ‖B (B.inverse x)‖ ^ 2 := (norm_sq_eq_pair_self hB _).symm
      _ = ‖x‖ ^ 2 := by rw [hx]
  have h2 : Real.sqrt c * ‖B.inverse x‖ ≤ ‖x‖ := by
    have h3 : (Real.sqrt c * ‖B.inverse x‖) ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]; exact h1
    nlinarith [norm_nonneg (B.inverse x), norm_nonneg x, Real.sqrt_nonneg c]
  rw [le_div_iff₀ hsc]; linarith

/-- If the closed ball centred at `x` of radius `r` is contained in the open unit ball, then
`‖x‖ + r < 1`. -/
theorem norm_add_lt_one_of_closedBall_subset_ball {x : ℝ⁴} {r : ℝ} (hr : 0 ≤ r)
    (h : closedBall x r ⊆ ball 0 1) : ‖x‖ + r < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hv : ‖stdB4 0‖ = 1 := OrthonormalBasis.norm_eq_one stdB4 0
    have hmem : r • stdB4 0 ∈ closedBall (0 : ℝ⁴) r := by
      simp [mem_closedBall, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv]
    have h1 := h hmem
    have h2 : ‖r • stdB4 0‖ = r := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv]
    rw [mem_ball, dist_zero_right, h2] at h1
    simpa using h1
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hdist : dist (x + (r / ‖x‖) • x) x = r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr hxpos.le), div_mul_cancel₀ _ hxpos.ne']
    have hmem : x + (r / ‖x‖) • x ∈ closedBall x r := by rw [mem_closedBall, hdist]
    have h1 := h hmem
    rw [mem_ball, dist_zero_right] at h1
    have hyn : ‖x + (r / ‖x‖) • x‖ = ‖x‖ + r := by
      rw [show x + (r / ‖x‖) • x = (1 + r / ‖x‖) • x by rw [add_smul, one_smul],
        norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + r / ‖x‖), add_mul, one_mul,
        div_mul_cancel₀ _ hxpos.ne']
    linarith [hyn ▸ h1]

/-- The trace of a product with a scalar multiple. -/
theorem trOp_mul_smul (S M : ℝ⁴ →L[ℝ] ℝ⁴) (k : ℝ) :
    trOp (S * (k • M)) = k * trOp (S * M) := by
  rw [show S * (k • M) = k • (S * M) from by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]]
  rw [trOp_smul]

/-! ## The symmetrization of a bilinear form -/

/-- The symmetrization of a continuous bilinear form. -/
noncomputable def symmBilin (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (Q + Q.flip)

theorem symmBilin_apply (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) (u v : ℝ⁴) :
    symmBilin Q u v = (Q u v + Q v u) / 2 := by
  simp only [symmBilin, smul_apply, add_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm]
  ring

theorem symmBilin_symm (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) (u v : ℝ⁴) :
    symmBilin Q u v = symmBilin Q v u := by
  rw [symmBilin_apply, symmBilin_apply]; ring

/-- The self-adjoint operator representing the symmetrized bilinear form. -/
noncomputable def symmOp (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  InnerProductSpace.continuousLinearMapOfBilin (symmBilin Q)

theorem symmOp_inner (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) (u v : ℝ⁴) :
    ⟪symmOp Q u, v⟫ = symmBilin Q u v := by
  simpa only [symmOp] using
    InnerProductSpace.continuousLinearMapOfBilin_apply (symmBilin Q) u v

theorem symmOp_isSymmetric (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) :
    LinearMap.IsSymmetric ((symmOp Q : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴) := by
  intro u v
  change ⟪(symmOp Q) u, v⟫ = ⟪u, (symmOp Q) v⟫
  calc ⟪(symmOp Q) u, v⟫ = symmBilin Q u v := symmOp_inner Q u v
    _ = symmBilin Q v u := symmBilin_symm Q u v
    _ = ⟪(symmOp Q) v, u⟫ := (symmOp_inner Q v u).symm
    _ = ⟪u, (symmOp Q) v⟫ := real_inner_comm _ _

theorem symmOp_quad (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) (u : ℝ⁴) :
    ⟪symmOp Q u, u⟫ = Q u u := by
  rw [symmOp_inner, symmBilin_apply]
  ring

/-- The symmetrized operator "solves" the same linear trace equation as `Q` itself. -/
theorem trOp_symmOp (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ)
    (hQ : ∑ i : Fin 4, Q (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single i (1:ℝ)) = 0) :
    trOp (symmOp Q) = 0 := by
  rw [trOp_eq_sum]
  have h1 : ∀ i : Fin 4, ⟪symmOp Q (stdB4 i), stdB4 i⟫
      = Q (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single i (1:ℝ)) := by
    intro i
    rw [symmOp_quad, stdB4_apply]
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  exact hQ

/-! ## Scaling of the ball mean value property -/

/-- The ball mean value property is preserved by a dilation. -/
theorem mvp_comp_smul {v : ℝ⁴ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {E S : Set ℝ⁴}
    (hmvp : ∀ x ∈ E, ∀ r : ℝ, 0 < r → closedBall x r ⊆ E → v x = ⨍ y in ball x r, v y)
    (hmap : ∀ z ∈ S, ρ • z ∈ E)
    (hballs : ∀ x ∈ S, ∀ r : ℝ, 0 < r → closedBall x r ⊆ S → closedBall (ρ • x) (ρ * r) ⊆ E) :
    ∀ x ∈ S, ∀ r : ℝ, 0 < r → closedBall x r ⊆ S →
      v (ρ • x) = ⨍ y in ball x r, v (ρ • y) := by
  intro x hx r hr hsub
  have hρr : 0 < ρ * r := mul_pos hρ hr
  have hA : (⨍ y in ball (ρ • x) (ρ * r), v y) = ⨍ z in ball (0 : ℝ⁴) (ρ * r), v (ρ • x + z) := by
    have h := Commons.Measure.Average.setAverage_ball_comp_smul_sub (n := 4) (x₀ := ρ • x)
      (r := ρ * r) (t := 1) one_pos hρr (fun y => v y)
    simpa using h
  have hB : (⨍ y in ball (0 : ℝ⁴) r, v (ρ • x + ρ • y))
      = ⨍ z in ball (0 : ℝ⁴) (ρ * r), v (ρ • x + z) :=
    Commons.Measure.Lebesgue.setAverage_comp_smul_ball (n := 4)
      (f := fun z => v (ρ • x + z)) hρ hr
  have hC : (⨍ y in ball x r, v (ρ • y)) = ⨍ z in ball (0 : ℝ⁴) r, v (ρ • x + ρ • z) := by
    have h := Commons.Measure.Average.setAverage_ball_comp_smul_sub (n := 4) (x₀ := x)
      (r := r) (t := 1) one_pos hr (fun y => v (ρ • y))
    simpa [smul_add] using h
  rw [hmvp (ρ • x) (hmap x hx) (ρ * r) hρr (hballs x hx r hr hsub), hA, hC, ← hB]

/-! ## The quadratic approximation -/

/-- **The linear theory of Proposition 4.1, UNIFORM in the base.**  The constant `C` depends only
on the ellipticity constants `c`, `c'`. -/
theorem linear_quadratic_approx_uniform {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ⁴ →L[ℝ] ℝ⁴) (hN : N.IsSymmetric)
      (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp N v, v⟫)
      (hcq' : ∀ v : ℝ⁴, ⟪cofOp N v, v⟫ ≤ c' * ‖v‖ ^ 2)
      (θ : ℝ) (_hθ : 0 < θ) (_hθ1 : 2 * θ * Real.sqrt (c' / c) ≤ 1 / 2) (w : ℝ⁴ → ℝ),
      ContinuousOn w (ball 0 1) →
      IsViscSolution (fun M => -trOp (cofOp N * M)) w (ball 0 1) →
      (∀ x ∈ ball 0 1, |w x| ≤ 1) →
      ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ),
        P₂.IsSymmetric ∧ trOp (cofOp N * P₂) = 0 ∧
        ∀ x ∈ closedBall 0 θ, |w x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ C * θ ^ 3 := by
  have hcc' : 0 < c' / c := div_pos hc' hc
  have hsq : 0 < Real.sqrt (c' / c) := Real.sqrt_pos.mpr hcc'
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.Analysis.Harmonic.quadratic_approx_of_harmonic_uniform
  refine ⟨C0 * (2 * Real.sqrt (c' / c)) ^ 3, by positivity, ?_⟩
  intro N hN hcq hcq' θ hθ hθ1 w hwcont hvisc hw
  have hθz : 0 < 2 * θ * Real.sqrt (c' / c) := by positivity
  have hθzhalf : 2 * θ * Real.sqrt (c' / c) ≤ 1 / 2 := hθ1
  obtain ⟨B, hBsym, hBB, hBinv, hmvp⟩ :=
    mvp_of_visc_linear hN hc hcq isOpen_ball hwcont hvisc
  have hBBi : B * B.inverse = 1 := hBinv.self_comp_inverse
  have hBiB : B.inverse * B = 1 := hBinv.inverse_comp_self
  set ρ : ℝ := 1 / (2 * Real.sqrt c')
  have hρpos : 0 < ρ := by positivity
  have hBnorm : ∀ u : ℝ⁴, ‖B u‖ ≤ Real.sqrt c' * ‖u‖ :=
    norm_le_sqrt_mul hBsym hc'.le (by rw [hBB]; exact hcq') 
  have hρc' : Real.sqrt c' * ρ = 1 / 2 := by
    rw [show ρ = 1 / (2 * Real.sqrt c') from rfl]
    field_simp
  have hBinvnorm : ∀ x : ℝ⁴, ‖B.inverse x‖ ≤ ‖x‖ / Real.sqrt c :=
    norm_inverse_le hBsym hc (by rw [hBB]; exact hcq) hBBi
  -- the rescaled function and its mean value property
  set v : ℝ⁴ → ℝ := fun y => w (B y)
  have hE : B ⁻¹' ball 0 1 = {y : ℝ⁴ | ‖B y‖ < 1} := by
    ext y; simp [mem_ball, dist_zero_right]
  have hmaps : ∀ z ∈ ball (0:ℝ⁴) 1, ρ • z ∈ B ⁻¹' ball 0 1 := by
    intro z hz
    rw [hE]
    have hz1 : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
    calc ‖B (ρ • z)‖ ≤ Real.sqrt c' * ‖ρ • z‖ := hBnorm _
      _ = Real.sqrt c' * (ρ * ‖z‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
      _ = (1/2) * ‖z‖ := by rw [← mul_assoc, hρc']
      _ < 1 := by linarith
  have hVcont : ContinuousOn (fun z : ℝ⁴ => v (ρ • z)) (ball 0 1) := by
    have h1 : Continuous (fun z : ℝ⁴ => B (ρ • z)) :=
      B.continuous.comp ((continuous_const : Continuous fun _ : ℝ⁴ => ρ).smul continuous_id)
    exact hwcont.comp h1.continuousOn hmaps
  have hVmvp : ∀ x ∈ ball (0:ℝ⁴) 1, ∀ r : ℝ, 0 < r → closedBall x r ⊆ ball 0 1 →
      v (ρ • x) = ⨍ y in ball x r, v (ρ • y) := by
    refine mvp_comp_smul hρpos hmvp hmaps ?_
    intro x hx r hr hsub z hz
    rw [hE]
    have hzr : ‖z - ρ • x‖ ≤ ρ * r := by
      have h := hz
      rw [mem_closedBall, dist_eq_norm] at h
      exact h
    have hxr : ‖x‖ + r < 1 := norm_add_lt_one_of_closedBall_subset_ball hr.le hsub
    have hzn : ‖z‖ ≤ ρ * (‖x‖ + r) := by
      have hbase : ‖z‖ ≤ ‖z - ρ • x‖ + ‖ρ • x‖ := by
        have h4 : (z - ρ • x) + ρ • x = z := by abel
        calc ‖z‖ = ‖(z - ρ • x) + ρ • x‖ := by rw [h4]
          _ ≤ ‖z - ρ • x‖ + ‖ρ • x‖ := norm_add_le _ _
      calc ‖z‖ ≤ ‖z - ρ • x‖ + ‖ρ • x‖ := hbase
        _ ≤ ρ * r + ρ * ‖x‖ := by
            refine add_le_add hzr ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
        _ = ρ * (‖x‖ + r) := by ring
    calc ‖B z‖ ≤ Real.sqrt c' * ‖z‖ := hBnorm _
      _ ≤ Real.sqrt c' * (ρ * (‖x‖ + r)) := by
            exact mul_le_mul_of_nonneg_left hzn (Real.sqrt_nonneg c')
      _ = (1/2) * (‖x‖ + r) := by rw [← mul_assoc, hρc']
      _ < 1 := by linarith
  have hVbound : ∀ z ∈ ball (0:ℝ⁴) 1, |v (ρ • z)| ≤ 1 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
    have h1 : ‖B (ρ • z)‖ < 1 := by
      have h2 : ‖B (ρ • z)‖ ≤ Real.sqrt c' * ‖ρ • z‖ := hBnorm _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos] at h2
      have h3 : Real.sqrt c' * (ρ * ‖z‖) = (1/2) * ‖z‖ := by rw [← mul_assoc, hρc']
      linarith
    have h4 := hw (B (ρ • z)) (by simpa [mem_ball, dist_zero_right] using h1)
    simpa [v] using h4
  have hVharm := Commons.Analysis.Harmonic.mvp_contDiff_harmonic (n := 4) (by norm_num) hVcont hVmvp
  obtain ⟨Q, q, t, hQtr, hQbound⟩ :=
    hC0 (fun z => v (ρ • z)) (2 * θ * Real.sqrt (c' / c)) hθz hθzhalf
      (hVharm.1.of_le le_top) hVharm.2 hVbound
  -- the transferred quadratic
  set A : ℝ⁴ →L[ℝ] ℝ⁴ := (1/ρ) • B.inverse
  have hBinvsym : ∀ x y : ℝ⁴, ⟪B.inverse x, y⟫ = ⟪x, B.inverse y⟫ :=
    fun x y => inverse_isSymmetric hBsym hBinv x y
  have hAdef2 : A = (1/ρ) • B.inverse := rfl
  have hAsym' : ∀ x y : ℝ⁴, ⟪A x, y⟫ = ⟪x, A y⟫ := by
    intro x y
    rw [hAdef2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      real_inner_smul_left, real_inner_smul_right, hBinvsym x y]
  have hAsym : A.IsSymmetric := fun x y => hAsym' x y
  have hQsym : ∀ x y : ℝ⁴, ⟪(symmOp Q) x, y⟫ = ⟪x, (symmOp Q) y⟫ :=
    fun x y => symmOp_isSymmetric Q x y
  have hmul : ∀ u : ℝ⁴, (A * symmOp Q * A) u = A (symmOp Q (A u)) := by
    intro u
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  have hquad : ∀ u : ℝ⁴, ⟪(A * symmOp Q * A) u, u⟫ = Q (A u) (A u) := by
    intro u
    rw [hmul u, hAsym' (symmOp Q (A u)) u, symmOp_quad]
  have hPsym' : ∀ x y : ℝ⁴,
      ⟪(A * symmOp Q * A) x, y⟫ = ⟪x, (A * symmOp Q * A) y⟫ := by
    intro x y
    rw [hmul x, hmul y]
    calc ⟪A (symmOp Q (A x)), y⟫ = ⟪symmOp Q (A x), A y⟫ := hAsym' (symmOp Q (A x)) y
      _ = ⟪A x, symmOp Q (A y)⟫ := hQsym (A x) (A y)
      _ = ⟪x, A (symmOp Q (A y))⟫ := hAsym' x (symmOp Q (A y))
  refine ⟨A * symmOp Q * A, q.comp A, t, fun x y => hPsym' x y, ?_, ?_⟩
  · -- the linearised equation is preserved
    have hAA : A * symmOp Q * A = ((1/ρ) * (1/ρ)) • (B.inverse * symmOp Q * B.inverse) := by
      rw [hAdef2]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    have h1 : (B * B) * (B.inverse * symmOp Q * B.inverse) = B * symmOp Q * B.inverse := by
      rw [show (B * B) * (B.inverse * symmOp Q * B.inverse)
          = B * ((B * B.inverse) * symmOp Q) * B.inverse from by noncomm_ring]
      rw [hBBi]
      simp only [one_mul]
    have h2 : trOp (B * symmOp Q * B.inverse) = trOp (symmOp Q) := by
      rw [trOp_mul_comm (B * symmOp Q) B.inverse]
      rw [show B.inverse * (B * symmOp Q) = (B.inverse * B) * symmOp Q from by noncomm_ring]
      rw [hBiB]
      simp only [one_mul]
    rw [← hBB, hAA, trOp_mul_smul, h1, h2, trOp_symmOp Q hQtr, mul_zero]
  · -- the approximation
    intro x hx
    have hxθ : ‖x‖ ≤ θ := by simpa [mem_closedBall, dist_zero_right] using hx
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hAz : A x ∈ closedBall (0 : ℝ⁴) (2 * θ * Real.sqrt (c' / c)) := by
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖A x‖ = 2 * Real.sqrt c' * ‖B.inverse x‖ := by
        rw [hAdef2, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0:ℝ) < 1/ρ)]
        congr 1
        rw [show ρ = 1 / (2 * Real.sqrt c') from rfl]
        field_simp
      rw [h1]
      have h2 : ‖B.inverse x‖ ≤ ‖x‖ / Real.sqrt c := hBinvnorm x
      have h3 : ‖x‖ / Real.sqrt c ≤ θ / Real.sqrt c := div_le_div_of_nonneg_right hxθ hsc.le
      have h4 : 2 * Real.sqrt c' * (θ / Real.sqrt c) = 2 * θ * (Real.sqrt c' / Real.sqrt c) := by
        field_simp
      have h5 : Real.sqrt (c' / c) = Real.sqrt c' / Real.sqrt c :=
        Real.sqrt_div (x := c') hc'.le c
      calc 2 * Real.sqrt c' * ‖B.inverse x‖ ≤ 2 * Real.sqrt c' * (θ / Real.sqrt c) :=
            mul_le_mul_of_nonneg_left (le_trans h2 h3) (by positivity)
        _ = 2 * θ * (Real.sqrt c' / Real.sqrt c) := h4
        _ = 2 * θ * Real.sqrt (c' / c) := by rw [h5]
    have hVAx : v (ρ • (A x)) = w x := by
      rw [hAdef2, ContinuousLinearMap.smul_apply, smul_smul, mul_one_div, div_self hρpos.ne',
        one_smul]
      simp only [v]
      rw [show B (B.inverse x) = x from by
        have h1 : (B * B.inverse) x = x := by rw [hBBi]; rfl
        rwa [ContinuousLinearMap.mul_apply] at h1]
    have hmain : |w x - (Q (A x) (A x) / 2 + q (A x) + t)| ≤
        C0 * (2 * θ * Real.sqrt (c' / c)) ^ 3 := by
      have h := hQbound (A x) hAz
      rw [hVAx] at h
      convert h using 2
      ring
    have hgoal : |w x - (⟪(A * symmOp Q * A) x, x⟫ / 2 + (q.comp A) x + t)| ≤
        (C0 * (2 * Real.sqrt (c' / c)) ^ 3) * θ ^ 3 := by
      have h1 : ⟪(A * symmOp Q * A) x, x⟫ = Q (A x) (A x) := hquad x
      have h2 : (q.comp A) x = q (A x) := ContinuousLinearMap.comp_apply q A x
      rw [h1, h2]
      have h3 : C0 * (2 * θ * Real.sqrt (c' / c)) ^ 3
          = (C0 * (2 * Real.sqrt (c' / c)) ^ 3) * θ ^ 3 := by ring
      rw [← h3]
      exact hmain
    exact hgoal

/-- The (non-uniform) form of the linear theory, with the base `N` fixed. -/
theorem linear_quadratic_approx {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) {c c' : ℝ}
    (hc : 0 < c) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp N v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp N v, v⟫ ≤ c' * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (_hθ : 0 < θ)
      (_hθ1 : 2 * θ * Real.sqrt (c' / c) ≤ 1 / 2) (w : ℝ⁴ → ℝ), ContinuousOn w (ball 0 1) →
      IsViscSolution (fun M => -trOp (cofOp N * M)) w (ball 0 1) →
      (∀ x ∈ ball 0 1, |w x| ≤ 1) →
      ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ),
        P₂.IsSymmetric ∧ trOp (cofOp N * P₂) = 0 ∧
        ∀ x ∈ closedBall 0 θ, |w x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ C * θ ^ 3 := by
  have hc' : 0 < c' := by
    have h1 : c * ‖stdB4 0‖ ^ 2 ≤ c' * ‖stdB4 0‖ ^ 2 := le_trans (hcq (stdB4 0)) (hcq' (stdB4 0))
    rw [OrthonormalBasis.norm_eq_one stdB4 0] at h1
    linarith
  obtain ⟨C, hCpos, hC⟩ := linear_quadratic_approx_uniform (c := c) (c' := c') hc hc'
  exact ⟨C, hCpos, hC N hN hcq hcq'⟩

end

end Submission
