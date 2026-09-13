/-
# The barrier of the growth lemma (Savin's Lemma 2.2)

The `enlarge opening` lemma of the sliding-paraboloid method (Savin, CPDE 32 (2007); Cabre;
Imbert--Silvestre; Li--Li; Lian--Zhang arXiv:2405.07199; Fan arXiv:2509.01138) uses the explicit
barrier

  `ψ(x) = P_{a,y₁}(x) + a r² φ(‖x - x₀‖/r)`,   `φ(t) = (1/p)(t^{-p} - 1)`   for `1/2 ≤ t ≤ 1`,

extended by the constant value `φ(1/2) = (2^p - 1)/p` for `t ≤ 1/2` and by `0` for `t ≥ 1`
(`p` a universal constant, e.g. `p ≥ 16 c'/c`).  On the annulus `r/2 < ‖x - x₀‖ < r`, with
`t = ‖x - x₀‖/r` and `u = (x - x₀)/‖x - x₀‖`, the eigenvalues of `D²ψ(x)` are

  `a((p+1) t^{-p-2} - 1)` (once, radial) and `-a(t^{-p-2} + 1)` (three times),

so with `α = (p+1)t^{-p-2} - 1`, `β = -t^{-p-2} - 1`,

  `D²ψ(x) = a • (α • P_u + β • (1 - P_u))`.

This file builds `ψ` and computes `Fop C ε (D²ψ)` and `cofOp (D²ψ)` on the annulus.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Savin.Diag
import Submission.Savin.Measure
import Submission.Savin.Sliding
import Submission.Savin.Mono
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_radial
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_affine_sub_div
import Submission.Commons.Analysis.Growth.cofop_growth_arith
import Submission.Commons.Analysis.Growth.fop_growth_arith

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-! ## The radial profile -/

/-- Clamping to `[1/2,1]`. -/
noncomputable def clampHalf (t : ℝ) : ℝ := max (min t 1) (1 / 2)

theorem clampHalf_le_one (t : ℝ) : clampHalf t ≤ 1 :=
  max_le (min_le_right _ _) (by norm_num)

theorem half_le_clampHalf (t : ℝ) : 1 / 2 ≤ clampHalf t := le_max_right _ _

theorem clampHalf_pos (t : ℝ) : 0 < clampHalf t := lt_of_lt_of_le (by norm_num) (half_le_clampHalf t)

theorem clampHalf_eq_self {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) : clampHalf t = t := by
  unfold clampHalf
  rw [min_eq_left h2, max_eq_left h1]

theorem clampHalf_one : clampHalf 1 = 1 := clampHalf_eq_self (by norm_num) le_rfl

theorem clampHalf_eq_one {t : ℝ} (h : 1 ≤ t) : clampHalf t = 1 := by
  unfold clampHalf
  rw [min_eq_right h, max_eq_left (by norm_num)]

theorem continuous_clampHalf : Continuous clampHalf := by
  unfold clampHalf
  exact (continuous_id.min continuous_const).max continuous_const

/-- The radial profile of the barrier: `φ(t) = (1/p)(clamp(t)^{-p} - 1)`. -/
noncomputable def growthProfile (p : ℝ) (t : ℝ) : ℝ :=
  (1 / p) * ((clampHalf t) ^ (-p) - 1)

/-- The barrier `x ↦ a r² φ(‖x - x₀‖/r)`. -/
noncomputable def growthBarrier (p a r : ℝ) (x₀ : ℝ⁴) : ℝ⁴ → ℝ :=
  fun x => a * r ^ 2 * growthProfile p (‖x - x₀‖ / r)

theorem growthProfile_apply (p t : ℝ) :
    growthProfile p t = (1 / p) * ((clampHalf t) ^ (-p) - 1) := rfl

theorem growthProfile_eq_of_mem {p t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) :
    growthProfile p t = (1 / p) * (t ^ (-p) - 1) := by
  simp only [growthProfile, clampHalf_eq_self h1 h2]

theorem growthProfile_one {p : ℝ} (hp : p ≠ 0) : growthProfile p 1 = 0 := by
  rw [growthProfile_eq_of_mem (by norm_num) le_rfl, Real.one_rpow]
  ring

theorem growthProfile_nonneg {p t : ℝ} (hp : 0 < p) : 0 ≤ growthProfile p t := by
  have h1 : 1 ≤ (clampHalf t) ^ (-p) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (clampHalf_pos t) (clampHalf_le_one t)
      (by linarith)
  have h2 : (0 : ℝ) ≤ 1 / p := by positivity
  simp only [growthProfile]
  nlinarith

theorem growthProfile_eq_zero_of_one_le {p t : ℝ} (h : 1 ≤ t) : growthProfile p t = 0 := by
  simp only [growthProfile, clampHalf_eq_one h, Real.one_rpow, sub_self, mul_zero]

theorem growthProfile_le {p t : ℝ} (hp : 0 < p) :
    growthProfile p t ≤ (1 / p) * (2 ^ p - 1) := by
  have h1 : (clampHalf t) ^ (-p) ≤ ((1 : ℝ) / 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (half_le_clampHalf t) (by linarith)
  have h2 : ((1 : ℝ) / 2) ^ (-p) = 2 ^ p := by
    rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num), inv_inv]
  have h3 : (0 : ℝ) ≤ 1 / p := by positivity
  simp only [growthProfile]
  rw [h2] at h1
  nlinarith

theorem continuous_growthProfile (p : ℝ) : Continuous (growthProfile p) := by
  unfold growthProfile
  exact continuous_const.mul (Continuous.sub
    (continuous_clampHalf.rpow_const fun x => Or.inl (ne_of_gt (clampHalf_pos x)))
    continuous_const)

theorem continuous_growthBarrier (p a r : ℝ) (x₀ : ℝ⁴) :
    Continuous (growthBarrier p a r x₀) := by
  unfold growthBarrier
  exact continuous_const.mul ((continuous_growthProfile p).comp
    ((continuous_id.sub continuous_const).norm.div_const r))

theorem growthBarrier_nonneg {p a r : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (x₀ x : ℝ⁴) :
    0 ≤ growthBarrier p a r x₀ x := by
  unfold growthBarrier
  exact mul_nonneg (mul_nonneg ha (sq_nonneg r)) (growthProfile_nonneg hp)

theorem growthBarrier_le {p a r : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (x₀ x : ℝ⁴) :
    growthBarrier p a r x₀ x ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) := by
  unfold growthBarrier
  exact mul_le_mul_of_nonneg_left (growthProfile_le hp) (mul_nonneg ha (sq_nonneg r))

theorem growthBarrier_eq_zero {p a r : ℝ} {x₀ x : ℝ⁴} (hr : 0 < r)
    (hx : r ≤ ‖x - x₀‖) : growthBarrier p a r x₀ x = 0 := by
  have ht : 1 ≤ ‖x - x₀‖ / r := (le_div_iff₀ hr).mpr (by simpa using hx)
  rw [growthBarrier, growthProfile_eq_zero_of_one_le ht, mul_zero]

/-! ## The unclamped radial function and its derivatives -/

/-- The unclamped radial profile in the variable `s = ‖ξ‖`. -/
noncomputable def barrierKappa (p a r s : ℝ) : ℝ :=
  a * r ^ 2 * ((1 / p) * (s ^ (-p) - 1))

theorem barrierKappa_eq (p a r s : ℝ) :
    barrierKappa p a r s = (a * r ^ 2 * (1 / p)) * (s ^ (-p) - 1) := by
  unfold barrierKappa; ring

theorem deriv_barrierKappa {p a r s : ℝ} (hp : p ≠ 0) :
    deriv (barrierKappa p a r) s = -a * r ^ 2 * s ^ (-p - 1) := by
  have hfun : barrierKappa p a r = fun s : ℝ => (a * r ^ 2 * (1 / p)) * (s ^ (-p) - 1) := by
    funext t; exact barrierKappa_eq p a r t
  rw [hfun, deriv_const_mul_field (a * r ^ 2 * (1 / p)), deriv_sub_const,
    Real.deriv_rpow_const]
  field_simp

theorem deriv_deriv_barrierKappa {p a r s : ℝ} (hp : p ≠ 0) :
    deriv (deriv (barrierKappa p a r)) s = a * r ^ 2 * (p + 1) * s ^ (-p - 2) := by
  have hfun : deriv (barrierKappa p a r) = fun s : ℝ => -a * r ^ 2 * s ^ (-p - 1) := by
    funext t; exact deriv_barrierKappa (a := a) (r := r) hp
  rw [hfun]
  rw [show (fun s : ℝ => -a * r ^ 2 * s ^ (-p - 1))
      = (fun s : ℝ => (-a * r ^ 2) * s ^ (-p - 1)) from by funext t; ring]
  rw [deriv_const_mul_field (-a * r ^ 2), Real.deriv_rpow_const]
  ring_nf

theorem contDiffAt_barrierKappa {p a r s : ℝ} (hs : s ≠ 0) :
    ContDiffAt ℝ 2 (barrierKappa p a r) s := by
  have hfun : barrierKappa p a r = fun s : ℝ => (a * r ^ 2 * (1 / p)) * (s ^ (-p) - 1) := by
    funext t; exact barrierKappa_eq p a r t
  rw [hfun]
  exact ContDiffAt.mul contDiffAt_const
    (ContDiffAt.sub (Real.contDiffAt_rpow_const_of_ne hs) contDiffAt_const)


/-! ## The Hessian of the barrier -/

/-- Congruence of second derivatives on an open set. -/
theorem fderiv_fderiv_congr_of_eqOn_open {φ ψ : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    (hs : IsOpen s) (hx : x ∈ s) (h : ∀ y ∈ s, φ y = ψ y) :
    fderiv ℝ (fderiv ℝ φ) x = fderiv ℝ (fderiv ℝ ψ) x := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 x] fderiv ℝ ψ := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.mem_of_superset (hs.mem_nhds hy) fun z hz => h z hz)
  exact h1.fderiv_eq

/-- `continuousLinearMapOfBilin` is additive. -/
theorem clmOfBilin_add (B₁ B₂ : ℝ⁴ →L⋆[ℝ] ℝ⁴ →L[ℝ] ℝ) :
    InnerProductSpace.continuousLinearMapOfBilin (B₁ + B₂)
      = InnerProductSpace.continuousLinearMapOfBilin B₁
        + InnerProductSpace.continuousLinearMapOfBilin B₂ := by
  refine ContinuousLinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  simp only [ContinuousLinearMap.add_apply, inner_add_left,
    InnerProductSpace.continuousLinearMapOfBilin_apply]

/-- `continuousLinearMapOfBilin` is homogeneous. -/
theorem clmOfBilin_smul (k : ℝ) (B : ℝ⁴ →L⋆[ℝ] ℝ⁴ →L[ℝ] ℝ) :
    InnerProductSpace.continuousLinearMapOfBilin (k • B)
      = k • InnerProductSpace.continuousLinearMapOfBilin B := by
  refine ContinuousLinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  rw [show (k • InnerProductSpace.continuousLinearMapOfBilin B) v
      = k • (InnerProductSpace.continuousLinearMapOfBilin B v) from
      smul_apply (InnerProductSpace.continuousLinearMapOfBilin B) k v,
    real_inner_smul_left, InnerProductSpace.continuousLinearMapOfBilin_apply,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  simp

/-- The Hessian operator of a `C²` function is symmetric. -/
theorem hessOp_symm_of_contDiffAt {φ : ℝ⁴ → ℝ} {x : ℝ⁴} (h : ContDiffAt ℝ 2 φ x) :
    (hessOp φ x).IsSymmetric := by
  have hs : IsSymmSndFDerivAt ℝ φ x := h.isSymmSndFDerivAt (by norm_num)
  intro v w
  change inner ℝ (InnerProductSpace.continuousLinearMapOfBilin
      (fderiv ℝ (fderiv ℝ φ) x) v) w
    = inner ℝ v (InnerProductSpace.continuousLinearMapOfBilin
      (fderiv ℝ (fderiv ℝ φ) x) w)
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply, real_inner_comm,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  exact hs v w

/-- A symmetric operator is determined by its quadratic form. -/
theorem clm_eq_of_inner_self_eq {S T : ℝ⁴ →L[ℝ] ℝ⁴} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (h : ∀ v : ℝ⁴, ⟪S v, v⟫ = ⟪T v, v⟫) : S = T := by
  have hD : ((S - T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴).IsSymmetric := hS.sub hT
  have hzero : ((S - T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴) = 0 := by
    rw [← LinearMap.IsSymmetric.inner_map_self_eq_zero hD]
    intro v
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply, inner_sub_left,
      sub_eq_zero]
    exact h v
  have h2 : (S - T : ℝ⁴ →L[ℝ] ℝ⁴) = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hv := congrArg (fun (f : ℝ⁴ →ₗ[ℝ] ℝ⁴) => f v) hzero
    simp only [LinearMap.zero_apply, ContinuousLinearMap.zero_apply] at hv
    exact hv
  rwa [sub_eq_zero] at h2

/-- The Hessian of the concave paraboloid `parab a y c` is `-a • 1`. -/
theorem hessOp_parab (a c : ℝ) (y x : ℝ⁴) :
    hessOp (parab a y c) x = -a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
  have hcont : ContDiffAt ℝ 2 (parab a y c) x :=
    ((contDiff_parab a c y).contDiffAt).of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)
  have hsym1 : (hessOp (parab a y c) x).IsSymmetric := hessOp_symm_of_contDiffAt hcont
  have hsym2 : (-a • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).IsSymmetric :=
    LinearMap.IsSymmetric.smul (c := -a) (by simp) LinearMap.IsSymmetric.one
  refine clm_eq_of_inner_self_eq hsym1 hsym2 fun v => ?_
  rw [show ⟪hessOp (parab a y c) x v, v⟫
      = (fderiv ℝ (fderiv ℝ (parab a y c)) x) v v from
    InnerProductSpace.continuousLinearMapOfBilin_apply
      (B := fderiv ℝ (fderiv ℝ (parab a y c)) x) v v]
  rw [hessian_parab_diag a c y x v]
  simp only [smul_apply, one_apply_eq_self, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The second derivative of a sum. -/
theorem hessOp_add {φ q : ℝ⁴ → ℝ} {x : ℝ⁴}
    (hφ : ContDiffAt ℝ 2 φ x) (hq : ContDiffAt ℝ 2 q x) :
    hessOp (fun y => φ y + q y) x = hessOp φ x + hessOp q x := by
  unfold hessOp
  rw [Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_add_of_contDiffAt hφ hq, clmOfBilin_add]

/-- The unit radial vector `(x - x₀)/‖x - x₀‖`. -/
noncomputable def radUnit (x₀ x : ℝ⁴) : ℝ⁴ := (‖x - x₀‖)⁻¹ • (x - x₀)

theorem radUnit_apply (x₀ x : ℝ⁴) : radUnit x₀ x = (‖x - x₀‖)⁻¹ • (x - x₀) := rfl

theorem norm_radUnit {x₀ x : ℝ⁴} (hx : x ≠ x₀) : ‖radUnit x₀ x‖ = 1 := by
  rw [radUnit_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)

theorem inner_radUnit (x₀ v x : ℝ⁴) :
    ⟪v, radUnit x₀ x⟫ = ⟪v, x - x₀⟫ / ‖x - x₀‖ := by
  rw [radUnit_apply, real_inner_smul_right, div_eq_inv_mul]

theorem inner_projOne_self (u v : ℝ⁴) : ⟪projOne u v, v⟫ = (⟪v, u⟫) ^ 2 := by
  rw [projOne_apply, real_inner_smul_left, real_inner_comm u v]
  ring

theorem inner_one_sub_projOne_self (u v : ℝ⁴) :
    ⟪(1 - projOne u) v, v⟫ = ‖v‖ ^ 2 - (⟪v, u⟫) ^ 2 := by
  rw [sub_apply, one_apply_eq_self, inner_sub_left,
    real_inner_self_eq_norm_sq, inner_projOne_self]

/-- **The Hessian of the radial barrier.**  For a `C²` profile `κ` and `ξ ≠ 0`,
`D²(κ ∘ ‖·‖)(ξ)` is the operator `κ''(‖ξ‖) P_ξ̂ + (κ'(‖ξ‖)/‖ξ‖)(1 - P_ξ̂)`. -/
theorem hessOp_radial {κ : ℝ → ℝ} {ξ : ℝ⁴} (hξ : ξ ≠ 0) (hκ : ContDiffAt ℝ 2 κ ‖ξ‖) :
    hessOp (fun ξ : ℝ⁴ => κ ‖ξ‖) ξ
      = (deriv (deriv κ) ‖ξ‖) • projOne (radUnit 0 ξ)
        + ((deriv κ ‖ξ‖) / ‖ξ‖) • (1 - projOne (radUnit 0 ξ)) := by
  have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hsymS : (hessOp (fun ξ : ℝ⁴ => κ ‖ξ‖) ξ).IsSymmetric :=
    hessOp_symm_of_contDiffAt (hκ.comp ξ (contDiffAt_norm ℝ hξ))
  have hsymT : ((deriv (deriv κ) ‖ξ‖) • projOne (radUnit 0 ξ)
      + ((deriv κ ‖ξ‖) / ‖ξ‖) • (1 - projOne (radUnit 0 ξ))).IsSymmetric :=
    LinearMap.IsSymmetric.add
      (LinearMap.IsSymmetric.smul (by simp) (projOne_isSymmetric _))
      (LinearMap.IsSymmetric.smul (by simp)
        (LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one (projOne_isSymmetric _)))
  refine clm_eq_of_inner_self_eq hsymS hsymT fun v => ?_
  rw [show ⟪hessOp (fun ξ : ℝ⁴ => κ ‖ξ‖) ξ v, v⟫
      = (fderiv ℝ (fderiv ℝ (fun ξ : ℝ⁴ => κ ‖ξ‖)) ξ) v v from
    InnerProductSpace.continuousLinearMapOfBilin_apply (B := fderiv ℝ (fderiv ℝ
      (fun ξ : ℝ⁴ => κ ‖ξ‖)) ξ) v v]
  rw [Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_radial hξpos hκ ξ v rfl]
  have hR : ⟪((deriv (deriv κ) ‖ξ‖) • projOne (radUnit 0 ξ)
        + ((deriv κ ‖ξ‖) / ‖ξ‖) • (1 - projOne (radUnit 0 ξ))) v, v⟫
      = (deriv (deriv κ) ‖ξ‖) * (⟪v, ξ⟫ / ‖ξ‖) ^ 2
        + ((deriv κ ‖ξ‖) / ‖ξ‖) * (‖v‖ ^ 2 - (⟪v, ξ⟫ / ‖ξ‖) ^ 2) := by
    rw [add_apply, inner_add_left, smul_apply, smul_apply, real_inner_smul_left,
      real_inner_smul_left, inner_projOne_self, inner_one_sub_projOne_self,
      inner_radUnit, sub_zero]
  rw [hR]


/-! ## The operator identity for the barrier -/

/-- The smooth (unclamped) version of the barrier. -/
noncomputable def barrierSmooth (p a r : ℝ) (x₀ : ℝ⁴) : ℝ⁴ → ℝ :=
  fun x => barrierKappa p a r ‖r⁻¹ • (x - x₀)‖

theorem barrierSmooth_apply (p a r : ℝ) (x₀ x : ℝ⁴) :
    barrierSmooth p a r x₀ x = barrierKappa p a r ‖r⁻¹ • (x - x₀)‖ := rfl

theorem norm_inv_smul_sub {r : ℝ} (hr : 0 < r) (x₀ x : ℝ⁴) :
    ‖r⁻¹ • (x - x₀)‖ = ‖x - x₀‖ / r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]

theorem contDiffAt_barrierKappa_norm {p a r : ℝ} {ξ : ℝ⁴} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ 2 (fun ξ : ℝ⁴ => barrierKappa p a r ‖ξ‖) ξ :=
  (contDiffAt_barrierKappa (a := a) (r := r) (norm_ne_zero_iff.mpr hξ)).comp ξ
    (contDiffAt_norm ℝ hξ)

theorem barrierSmooth_eq_growthBarrier {p a r : ℝ} (hr : 0 < r) {x₀ x : ℝ⁴}
    (h1 : 1 / 2 ≤ ‖x - x₀‖ / r) (h2 : ‖x - x₀‖ / r ≤ 1) :
    barrierSmooth p a r x₀ x = growthBarrier p a r x₀ x := by
  rw [barrierSmooth_apply]
  rw [norm_inv_smul_sub hr]
  rw [barrierKappa, growthBarrier, growthProfile_eq_of_mem h1 h2]

theorem radUnit_inv_smul {x₀ x : ℝ⁴} {r : ℝ} (hx : x ≠ x₀) (hr : 0 < r) :
    radUnit 0 (r⁻¹ • (x - x₀)) = radUnit x₀ x := by
  have hσ : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  simp only [radUnit_apply, sub_zero]
  rw [norm_inv_smul_sub hr, smul_smul]
  congr 1
  field_simp

theorem hessOp_barrierSmooth {p a r : ℝ} {x₀ x : ℝ⁴} (hr : 0 < r) (hx : x ≠ x₀) :
    hessOp (barrierSmooth p a r x₀) x
      = (r⁻¹ * r⁻¹) • hessOp (fun ξ : ℝ⁴ => barrierKappa p a r ‖ξ‖)
          (r⁻¹ • (x - x₀)) := by
  have hne : r⁻¹ • (x - x₀) ≠ 0 := by
    rw [smul_ne_zero_iff, sub_ne_zero]
    exact ⟨inv_ne_zero (ne_of_gt hr), hx⟩
  have hmain : fderiv ℝ (fderiv ℝ (barrierSmooth p a r x₀)) x
      = (r⁻¹ * r⁻¹) • fderiv ℝ (fderiv ℝ (fun ξ : ℝ⁴ => barrierKappa p a r ‖ξ‖))
          (r⁻¹ • (x - x₀)) := by
    unfold barrierSmooth
    exact Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_affine_sub_div hr.ne'
      (contDiffAt_barrierKappa_norm (p := p) (a := a) (r := r) hne)
  unfold hessOp
  rw [hmain, clmOfBilin_smul]

/-- The explicit operator `a • (α • P_u + β • (1 - P_u))` produced by the barrier. -/
noncomputable def growthOp (p a r : ℝ) (x₀ x : ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  a • (((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1) • projOne (radUnit x₀ x)
    + (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1) • (1 - projOne (radUnit x₀ x)))

theorem one_eq_projOne_add (u : ℝ⁴) :
    (1 : ℝ⁴ →L[ℝ] ℝ⁴) = projOne u + (1 - projOne u) := by
  rw [add_comm, sub_add_cancel]

theorem smul_split {P : ℝ⁴ →L[ℝ] ℝ⁴} {c d e f : ℝ} :
    c • P + d • (1 - P) + (e • P + f • (1 - P))
      = (c + e) • P + (d + f) • (1 - P) := by
  have h : c • P + d • (1 - P) + (e • P + f • (1 - P))
      = (c • P + e • P) + (d • (1 - P) + f • (1 - P)) := by abel
  rw [h, ← add_smul c e P, ← add_smul d f (1 - P)]

/-- **The Hessian of the barrier function on the annulus.** -/
theorem hessOp_growthFunction {p a c r : ℝ} {y x₀ x : ℝ⁴} (hp : 0 < p) (hr : 0 < r)
    (hx1 : r / 2 < ‖x - x₀‖) (hx2 : ‖x - x₀‖ < r) :
    hessOp (fun z => parab a y c z + growthBarrier p a r x₀ z) x
      = growthOp p a r x₀ x := by
  have hxne : x ≠ x₀ := by
    intro h; rw [h, sub_self, norm_zero] at hx1; linarith
  have hne : r⁻¹ • (x - x₀) ≠ 0 := by
    rw [smul_ne_zero_iff, sub_ne_zero]
    exact ⟨inv_ne_zero (ne_of_gt hr), hxne⟩
  have hopen : IsOpen {z : ℝ⁴ | r / 2 < ‖z - x₀‖ ∧ ‖z - x₀‖ < r} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const |>.norm)).inter
      (isOpen_lt (continuous_id.sub continuous_const |>.norm) continuous_const)
  have heq : ∀ z ∈ {z : ℝ⁴ | r / 2 < ‖z - x₀‖ ∧ ‖z - x₀‖ < r},
      parab a y c z + growthBarrier p a r x₀ z = parab a y c z + barrierSmooth p a r x₀ z := by
    intro z hz
    have h1 : 1 / 2 ≤ ‖z - x₀‖ / r := by
      rw [le_div_iff₀ hr]; linarith [hz.1]
    have h2 : ‖z - x₀‖ / r ≤ 1 := by
      rw [div_le_one₀ hr]; exact hz.2.le
    exact congrArg (parab a y c z + ·)
      (barrierSmooth_eq_growthBarrier (p := p) (a := a) hr h1 h2).symm
  have hcongr := fderiv_fderiv_congr_of_eqOn_open hopen ⟨hx1, hx2⟩ heq
  have hstep : hessOp (fun z => parab a y c z + growthBarrier p a r x₀ z) x
      = hessOp (fun z => parab a y c z + barrierSmooth p a r x₀ z) x := by
    unfold hessOp
    rw [hcongr]
  have hparab : ContDiffAt ℝ 2 (parab a y c) x :=
    ((contDiff_parab a c y).contDiffAt).of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)
  have hbar : ContDiffAt ℝ 2 (barrierSmooth p a r x₀) x :=
    (contDiffAt_barrierKappa (a := a) (r := r) (norm_ne_zero_iff.mpr hne)).comp x
      ((contDiffAt_norm ℝ hne).comp x
        ((contDiffAt_id (x := x)).sub contDiffAt_const |>.const_smul (r⁻¹)))
  rw [hstep, hessOp_add hparab hbar, hessOp_parab, hessOp_barrierSmooth hr hxne,
    hessOp_radial (ξ := r⁻¹ • (x - x₀)) hne (contDiffAt_barrierKappa (a := a) (r := r)
      (norm_ne_zero_iff.mpr hne))]
  rw [radUnit_inv_smul hxne hr, norm_inv_smul_sub hr,
    deriv_barrierKappa (p := p) (a := a) (r := r) hp.ne',
    deriv_deriv_barrierKappa (p := p) (a := a) (r := r) hp.ne']
  have hrne : r ≠ 0 := ne_of_gt hr
  have h₁ : -a + r⁻¹ * r⁻¹ * (a * r ^ 2 * (p + 1) * (‖x - x₀‖ / r) ^ (-p - 2))
      = a * ((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1) := by
    have hrr : r⁻¹ * r⁻¹ * (a * r ^ 2 * (p + 1) * (‖x - x₀‖ / r) ^ (-p - 2))
        = a * (p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) := by
      rw [show r⁻¹ * r⁻¹ * (a * r ^ 2 * (p + 1) * (‖x - x₀‖ / r) ^ (-p - 2))
          = a * (p + 1) * (r⁻¹ * r⁻¹ * r ^ 2) * (‖x - x₀‖ / r) ^ (-p - 2) from by ring]
      rw [show r⁻¹ * r⁻¹ * r ^ 2 = 1 from by field_simp]
      ring
    rw [hrr]; ring
  have h₂ : -a + r⁻¹ * r⁻¹
        * (-a * r ^ 2 * (‖x - x₀‖ / r) ^ (-p - 1) / (‖x - x₀‖ / r))
      = a * (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1) := by
    have ht : (0 : ℝ) < ‖x - x₀‖ / r := by
      have h0 : 0 < ‖x - x₀‖ := by linarith
      positivity
    have hsplit : (‖x - x₀‖ / r) ^ (-p - 1) / (‖x - x₀‖ / r)
        = (‖x - x₀‖ / r) ^ (-p - 2) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (‖x - x₀‖ / r), ← Real.rpow_add ht]
      congr 1; ring
    have hfac : -a * r ^ 2 * (‖x - x₀‖ / r) ^ (-p - 1) / (‖x - x₀‖ / r)
        = -a * r ^ 2 * ((‖x - x₀‖ / r) ^ (-p - 1) / (‖x - x₀‖ / r)) := by ring
    rw [hfac, hsplit]
    have hrr : r⁻¹ * r⁻¹ * (-a * r ^ 2 * (‖x - x₀‖ / r) ^ (-p - 2))
        = -a * (‖x - x₀‖ / r) ^ (-p - 2) := by
      rw [show r⁻¹ * r⁻¹ * (-a * r ^ 2 * (‖x - x₀‖ / r) ^ (-p - 2))
          = -a * (r⁻¹ * r⁻¹ * r ^ 2) * (‖x - x₀‖ / r) ^ (-p - 2) from by ring]
      rw [show r⁻¹ * r⁻¹ * r ^ 2 = 1 from by field_simp]
      ring
    rw [hrr]; ring
  rw [show -a • (1 : ℝ⁴ →L[ℝ] ℝ⁴)
      = -a • (projOne (radUnit x₀ x) + (1 - projOne (radUnit x₀ x))) from
        congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => -a • T) (one_eq_projOne_add (radUnit x₀ x))]
  rw [smul_add, smul_add, smul_smul, smul_smul]
  rw [smul_split (c := -a) (d := -a)
    (e := (r⁻¹ * r⁻¹) * (a * r ^ 2 * (p + 1) * (‖x - x₀‖ / r) ^ (-p - 2)))
    (f := (r⁻¹ * r⁻¹)
      * (-a * r ^ 2 * (‖x - x₀‖ / r) ^ (-p - 1) / (‖x - x₀‖ / r)))]
  rw [h₁, h₂]
  unfold growthOp
  rw [smul_add, smul_smul, smul_smul]


/-! ## The sign of `Fop` and the monotonicity range on the annulus -/

theorem pairOp_projOne (C : ℝ⁴ →L[ℝ] ℝ⁴) (u : ℝ⁴) : pairOp C (projOne u) = ⟪C u, u⟫ := by
  unfold pairOp
  rw [show (∑ i : Fin 4, ⟪C ((projOne u) (stdB4 i)), stdB4 i⟫)
      = ∑ i : Fin 4, ⟪stdB4 i, u⟫ * ⟪C u, stdB4 i⟫
      from Finset.sum_congr rfl fun i _ => by
        rw [projOne_apply, map_smul, real_inner_smul_left]]
  rw [show (∑ i : Fin 4, ⟪stdB4 i, u⟫ * ⟪C u, stdB4 i⟫)
      = ∑ i : Fin 4, ⟪u, stdB4 i⟫ * ⟪stdB4 i, C u⟫
      from Finset.sum_congr rfl fun i _ => by
        rw [real_inner_comm (stdB4 i) u, real_inner_comm (C u) (stdB4 i)]]
  rw [← real_inner_comm (C u) u]
  exact stdB4.sum_inner_mul_inner u (C u)

theorem pairOp_projOneCombination {C : ℝ⁴ →L[ℝ] ℝ⁴} {u : ℝ⁴} (hu : ‖u‖ = 1) (α β : ℝ) :
    pairOp C (α • projOne u + β • (1 - projOne u))
      = α * ⟪C u, u⟫ + β * (trOp C - ⟪C u, u⟫) := by
  rw [pairOp_add, pairOp_smul, pairOp_smul, pairOp_sub, pairOp_one, pairOp_projOne]

theorem s2_smul (k : ℝ) (M : ℝ⁴ →L[ℝ] ℝ⁴) : s2 (k • M) = k ^ 2 * s2 M := by
  unfold s2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i < j
  · simp only [h, if_true, smul_apply, real_inner_smul_left]
    ring
  · simp only [h, if_false, mul_zero]

/-- `Fop` is homogeneous: scaling the matrix by `λ` is the same as scaling the value by `λ` and the
perturbation parameter by `λ`.  This is what makes all the rescalings of the small-perturbation
theory work: rescaling changes `ε` into `ε λ`. -/
theorem Fop_smul (C : ℝ⁴ →L[ℝ] ℝ⁴) (ε k : ℝ) (M : ℝ⁴ →L[ℝ] ℝ⁴) :
    Fop C ε (k • M) = k * Fop C (ε * k) M := by
  unfold Fop
  rw [pairOp_smul, s2_smul]
  ring


theorem trOp_growthOp {p a r : ℝ} {x₀ x : ℝ⁴} (hu : ‖radUnit x₀ x‖ = 1) :
    trOp (growthOp p a r x₀ x)
      = a * ((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1
          + 3 * (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1)) := by
  rw [growthOp, trOp_smul, trOp_add, trOp_smul, trOp_smul, trOp_sub, trOp_one,
    show trOp (projOne (radUnit x₀ x)) = 1 from by rw [trOp_projOne, hu]; norm_num]
  ring

/-- **Monotonicity range.**  With `4 ≤ p` and `12 ε a 2^{p+2} ≤ c` the operator
`C + ε • cofOp (growthOp p a r x₀ x)` is positive semidefinite, so that `Fop` is monotone on the
range of Hessians produced by the barrier. -/
theorem cofOp_growthOp_nonneg {C : ℝ⁴ →L[ℝ] ℝ⁴} {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫)
    {ε a p r : ℝ} (hε : 0 < ε) (ha : 0 < a) (hp : 4 ≤ p) (hr : 0 < r) {x₀ x : ℝ⁴}
    (hx1 : r / 2 < ‖x - x₀‖) (hx2 : ‖x - x₀‖ < r)
    (hεa : 12 * ε * a * 2 ^ (p + 2) ≤ c) :
    ∀ v : ℝ⁴, 0 ≤ ⟪(C + ε • cofOp (growthOp p a r x₀ x)) v, v⟫ := by
  intro v
  have hxne : x ≠ x₀ := by
    intro h; rw [h, sub_self, norm_zero] at hx1; linarith
  have hu : ‖radUnit x₀ x‖ = 1 := norm_radUnit hxne
  have ht0 : 0 < ‖x - x₀‖ / r := by
    have h0 : 0 < ‖x - x₀‖ := by linarith
    positivity
  have ht1 : ‖x - x₀‖ / r ≤ 1 := by rw [div_le_one₀ hr]; exact hx2.le
  have hτ1 : 1 ≤ (‖x - x₀‖ / r) ^ (-p - 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hτ2 : (‖x - x₀‖ / r) ^ (-p - 2) ≤ 2 ^ (p + 2) := by
    have h : (1 : ℝ) / 2 ≤ ‖x - x₀‖ / r := by rw [le_div_iff₀ hr]; linarith [hx1]
    have hle : (‖x - x₀‖ / r) ^ (-p - 2) ≤ ((1 : ℝ) / 2) ^ (-p - 2) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) h (by linarith)
    have h2 : ((1 : ℝ) / 2) ^ (-p - 2) = 2 ^ (p + 2) := by
      rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
        show -p - 2 = -(p + 2) from by ring, Real.rpow_neg (by norm_num), inv_inv]
    rw [h2] at hle; exact hle
  have hsnn : 0 ≤ (⟪v, radUnit x₀ x⟫) ^ 2 := sq_nonneg _
  have hsw : (⟪v, radUnit x₀ x⟫) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h1 : |⟪v, radUnit x₀ x⟫| ≤ ‖v‖ * ‖radUnit x₀ x‖ := abs_real_inner_le_norm v _
    rw [hu, mul_one] at h1
    nlinarith [sq_abs (⟪v, radUnit x₀ x⟫), abs_nonneg (⟪v, radUnit x₀ x⟫), h1]
  have hmain : ⟪(C + ε • cofOp (growthOp p a r x₀ x)) v, v⟫
      = ⟪C v, v⟫ + ε * ⟪cofOp (growthOp p a r x₀ x) v, v⟫ := by
    rw [add_apply, inner_add_left, smul_apply, real_inner_smul_left]
  have hqT : ⟪cofOp (growthOp p a r x₀ x) v, v⟫
      = a * ((3 * (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1)) * (⟪v, radUnit x₀ x⟫) ^ 2
          + (((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1)
              + 2 * (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1))
            * (‖v‖ ^ 2 - (⟪v, radUnit x₀ x⟫) ^ 2)) := by
    rw [cofOp, sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, trOp_growthOp hu]
    have hv : (growthOp p a r x₀ x) v
        = a • ((-((‖x - x₀‖ / r) ^ (-p - 2)) - 1) • v
            + (((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1)
                - (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1)) • (⟪v, radUnit x₀ x⟫ • radUnit x₀ x)) := by
      rw [growthOp, smul_apply, projOneCombination_apply hu]
    rw [hv, real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_comm (radUnit x₀ x) v]
    ring
  rw [hmain, hqT]
  have h1 := hcq v
  have h2 := Commons.Analysis.Growth.cofop_growth_arith (a := a) (c := c) (p := p)
    (τ := (‖x - x₀‖ / r) ^ (-p - 2)) (s := (⟪v, radUnit x₀ x⟫) ^ 2) (w := ‖v‖ ^ 2) (ε := ε)
    hc ha hε hsnn hsw hτ1 hτ2 hp hεa
  linarith

/-- **`Fop` is positive on the annulus.**  With `p ≥ 16 c'/c + 2` and
`48 ε a 2^{2p+4} ≤ c`, the barrier function is a strict supersolution of `Fop C ε = 0`. -/
theorem Fop_growthOp_pos {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) (hcq' : ∀ v : ℝ⁴, ⟪C v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {ε a p r : ℝ} (hε : 0 < ε) (ha : 0 < a) (hp : 0 < p) (hr : 0 < r) {x₀ x : ℝ⁴}
    (hx1 : r / 2 < ‖x - x₀‖) (hx2 : ‖x - x₀‖ < r)
    (hpbig : 16 * c' / c + 2 ≤ p) (hεa : 48 * ε * a * 2 ^ (2 * p + 4) ≤ c) :
    0 < Fop C ε (growthOp p a r x₀ x) := by
  have hxne : x ≠ x₀ := by
    intro h; rw [h, sub_self, norm_zero] at hx1; linarith
  have hu : ‖radUnit x₀ x‖ = 1 := norm_radUnit hxne
  have ht0 : 0 < ‖x - x₀‖ / r := by
    have h0 : 0 < ‖x - x₀‖ := by linarith
    positivity
  have ht1 : ‖x - x₀‖ / r ≤ 1 := by rw [div_le_one₀ hr]; exact hx2.le
  have hτ1 : 1 ≤ (‖x - x₀‖ / r) ^ (-p - 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hτ2 : (‖x - x₀‖ / r) ^ (-p - 2) ≤ 2 ^ (p + 2) := by
    have h : (1 : ℝ) / 2 ≤ ‖x - x₀‖ / r := by rw [le_div_iff₀ hr]; linarith [hx1]
    have hle : (‖x - x₀‖ / r) ^ (-p - 2) ≤ ((1 : ℝ) / 2) ^ (-p - 2) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) h (by linarith)
    have h2 : ((1 : ℝ) / 2) ^ (-p - 2) = 2 ^ (p + 2) := by
      rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
        show -p - 2 = -(p + 2) from by ring, Real.rpow_neg (by norm_num), inv_inv]
    rw [h2] at hle; exact hle
  have htrC : trOp C ≤ 4 * c' := by
    rw [trOp_eq_sum]
    calc ∑ i : Fin 4, ⟪C (stdB4 i), stdB4 i⟫ ≤ ∑ i : Fin 4, c' * ‖stdB4 i‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hcq' (stdB4 i)
      _ = 4 * c' := by
          simp only [stdB4.orthonormal.1, one_pow, mul_one, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hcu : c ≤ ⟪C (radUnit x₀ x), radUnit x₀ x⟫ := by
    have h := hcq (radUnit x₀ x)
    simpa [hu] using h
  have hcp : 0 < c' := by
    have h1 := hcq (stdB4 0)
    have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    rw [h3] at h1 h2
    nlinarith
  have hmain : Fop C ε (growthOp p a r x₀ x)
      = a * (((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1)
            * ⟪C (radUnit x₀ x), radUnit x₀ x⟫
          + (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1)
            * (trOp C - ⟪C (radUnit x₀ x), radUnit x₀ x⟫))
        + ε * (a ^ 2 * (3 * ((p + 1) * (‖x - x₀‖ / r) ^ (-p - 2) - 1)
            * (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1)
          + 3 * (-((‖x - x₀‖ / r) ^ (-p - 2)) - 1) ^ 2)) := by
    rw [Fop, growthOp, pairOp_smul, pairOp_projOneCombination hu, s2_smul,
      s2_projOne_combination hu]
  rw [hmain]
  exact Commons.Analysis.Growth.fop_growth_arith ha hc hε hcu htrC hτ1 hτ2
    (by have h : 0 ≤ 16 * c' / c := div_nonneg (by positivity) hc.le; linarith) hpbig hεa

end

end Submission
