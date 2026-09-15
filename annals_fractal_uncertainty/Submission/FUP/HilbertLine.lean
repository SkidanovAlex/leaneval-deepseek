import Submission.FUP.SecondDerivSum
import Submission.Commons.MeasureTheory.Integral.abs_integral_Ioi_sub_neg_div_le
import Submission.Commons.Analysis.Calculus.norm_fderiv_sub_le
import Submission.Commons.Analysis.Calculus.abs_integral_Ioi_slope_le_integral_abs_div_sq
import Submission.Commons.Analysis.Calculus.integral_Ioi_slope_eq_integral_div_sq
import Submission.Commons.MeasureTheory.Integral.integral_indicator_inv_sq_abs_ge

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, IX: the Hilbert transform of the derivative along a line

This module formalises the second estimate of §4, `eq:estimate_H_tilde_omega_k_sum`:

  `∑_k sup_{x ∈ ℓ} |H[ω̃_k|_ℓ'](x)| ≲ C_reg + C_gr`.

For a line `ℓ = {x + t ŷ}` the quantity `H[ω̃_k|_ℓ'](x)` is

  `(1/π) ∫_0^∞ (∂_ŷω̃_k(x + t ŷ) - ∂_ŷω̃_k(x - t ŷ))/t dt`,

an absolutely convergent integral because `ω̃_k` is compactly supported and `C¹`.  We formalise
it as `hilbertLine (ω̃_k) x ŷ`.

The regimes of the paper (with `x₀` the point of `ℓ` closest to the origin and `m₀` the least
integer with `‖x₀‖ ≤ 2^{m₀+1}`):

* `2^{k+1} < ‖x₀‖`: the support annulus of `ω̃_k` misses `ℓ` entirely, so the transform vanishes;
* `m₀ ≤ k ≤ m₀ + 6`: the crude bound `|H| ≤ 2 L (ρ + ‖x‖)` (`abs_hilbertLine_le`) with the
  Lipschitz constant `L = C_reg C̃ 2^{-k}` of `∂_ŷω̃_k` and `ρ = 2^{k+1}`;
* `k > m₀ + 6`: integration by parts
  (`Commons.Analysis.Calculus.integral_Ioi_slope_eq_integral_div_sq` in its rescaled form) turns
  the transform into `(1/π)∫_ℝ ω̃_k(x₀+tŷ)/t² dt`, which is bounded by `|q_k|` plus the
  translation error `C_reg C̃ ‖x₀‖ 2^{-k}` (`abs_hilbertLine_le_integral`).
-/

/-- The directional derivative `∂_y f(z)`. -/
noncomputable def dirDeriv (f : ℝᵈ → ℝ) (z y : ℝᵈ) : ℝ := fderiv ℝ f z y

/-- The Hilbert transform of `∂_y f` along the line `{x + t y}`, evaluated at `x`. -/
noncomputable def hilbertLine (f : ℝᵈ → ℝ) (x y : ℝᵈ) : ℝ :=
  (1 / π) * ∫ t in Set.Ioi (0 : ℝ),
    (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t

@[simp] lemma dirDeriv_apply (f : ℝᵈ → ℝ) (z y : ℝᵈ) : dirDeriv f z y = fderiv ℝ f z y := rfl

lemma hilbertLine_def (f : ℝᵈ → ℝ) (x y : ℝᵈ) :
    hilbertLine f x y = (1 / π) * ∫ t in Set.Ioi (0 : ℝ),
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t := rfl

/-- **The chain rule along a line**: `d/dt f(x + t y) = ∂_y f(x + t y)`. -/
lemma deriv_comp_line {f : ℝᵈ → ℝ} (hdiff : Differentiable ℝ f) (x y : ℝᵈ) (t : ℝ) :
    deriv (fun s : ℝ => f (x + s • y)) t = dirDeriv f (x + t • y) y := by
  have hg : HasDerivAt (fun s : ℝ => x + s • y) y t := by
    have h1 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    simpa using h1.const_add x
  have hf : HasFDerivAt f (fderiv ℝ f (x + t • y)) (x + t • y) :=
    (hdiff (x + t • y)).hasFDerivAt
  exact (hf.comp_hasDerivAt t hg).deriv

/-- `ω̃_k` vanishes on a neighbourhood of any point of norm `> 2^{k+1}`. -/
lemma omegaTildePiece_eventuallyEq_zero_of_norm_gt (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (hx : (2 : ℝ) ^ (k + 1) < ‖x‖) : omegaTildePiece (d := d) k w =ᶠ[𝓝 x] 0 := by
  have hmem : Metric.ball x (‖x‖ - (2 : ℝ) ^ (k + 1)) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (sub_pos.mpr hx)
  filter_upwards [hmem] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  refine omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt ?_)
  have h : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  rw [norm_sub_rev x y] at h
  linarith

/-- If `f` vanishes in a neighbourhood of a point then so does every directional derivative
there. -/
lemma dirDeriv_eq_zero_of_eventuallyEq_zero {f : ℝᵈ → ℝ} {z y : ℝᵈ}
    (h : f =ᶠ[𝓝 z] 0) : dirDeriv f z y = 0 := by
  have h1 : HasFDerivAt f (0 : ℝᵈ →L[ℝ] ℝ) z :=
    (hasFDerivAt_const (x := z) (c := (0 : ℝ))).congr_of_eventuallyEq h
  have h2 : fderiv ℝ f z = 0 := h1.fderiv
  rw [dirDeriv_apply, h2]
  simp

/-- **Regime 1**: if the line misses the support annulus of `ω̃_k`, the Hilbert transform of the
derivative vanishes. -/
lemma hilbertLine_omegaTildePiece_eq_zero (k : ℕ) (w : ℝᵈ → ℝ) (x₀ y : ℝᵈ) (hy : ‖y‖ = 1)
    (hperp : inner ℝ x₀ y = 0) (hmiss : (2 : ℝ) ^ (k + 1) < ‖x₀‖) :
    hilbertLine (omegaTildePiece (d := d) k w) x₀ y = 0 := by
  have hzero : ∀ t : ℝ, dirDeriv (omegaTildePiece (d := d) k w) (x₀ + t • y) y = 0 := by
    intro t
    refine dirDeriv_eq_zero_of_eventuallyEq_zero ?_
    refine omegaTildePiece_eventuallyEq_zero_of_norm_gt k w ?_
    linarith [norm_add_smul_ge_of_inner_eq_zero hy hperp t]
  have hz : ∀ t : ℝ, (dirDeriv (omegaTildePiece (d := d) k w) (x₀ + t • y) y
      - dirDeriv (omegaTildePiece (d := d) k w) (x₀ - t • y) y) / t = 0 := by
    intro t
    have h1 := hzero t
    have h2 : dirDeriv (omegaTildePiece (d := d) k w) (x₀ - t • y) y = 0 := by
      have h := hzero (-t)
      simpa [sub_eq_add_neg, neg_smul] using h
    rw [h1, h2, sub_zero, zero_div]
  rw [hilbertLine_def]
  simp only [hz]
  rw [integral_zero, mul_zero]

/-! ## The crude bound (regime 2) -/

/-- **The crude bound for the Hilbert transform of the derivative.**  If `∂_y f` is `L`-Lipschitz
and `f` is supported in the ball of radius `ρ`, then `|H[∂_y f]| ≤ 2 L (ρ + ‖x‖)`: the integrand
is bounded by `2L` and vanishes for `|t| > ρ + ‖x‖`. -/
lemma abs_hilbertLine_le (f : ℝᵈ → ℝ) (x y : ℝᵈ) (hy : ‖y‖ = 1)
    {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hlip : ∀ z₁ z₂ : ℝᵈ, ‖fderiv ℝ f z₁ - fderiv ℝ f z₂‖ ≤ L * ‖z₁ - z₂‖)
    (hsupp : ∀ z : ℝᵈ, ρ < ‖z‖ → fderiv ℝ f z = 0) :
    |hilbertLine f x y| ≤ 2 * L * (ρ + ‖x‖) := by
  have h1 : |∫ t in Set.Ioi (0 : ℝ),
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t| ≤ 2 * L * (ρ + ‖x‖) := by
    refine Commons.MeasureTheory.Integral.abs_integral_Ioi_sub_neg_div_le
      (fun z => dirDeriv f z y) hL hρ ?_ ?_ x y hy
    · intro a b
      have h := hlip a b
      rw [dirDeriv_apply, dirDeriv_apply]
      have h1 : |fderiv ℝ f a y - fderiv ℝ f b y| ≤ L * ‖a - b‖ := by
        rw [← sub_apply, ← Real.norm_eq_abs]
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [hy, mul_one]
        exact h
      exact h1
    · intro z hz
      rw [dirDeriv_apply, hsupp z hz]
      simp
  rw [hilbertLine_def]
  have hπ1 : (1 : ℝ) / π ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < π), one_mul]
    linarith [Real.pi_gt_three]
  calc |(1 / π) * ∫ t in Set.Ioi (0 : ℝ),
        (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t|
      = (1 / π) * |∫ t in Set.Ioi (0 : ℝ),
          (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
    _ ≤ 1 * |∫ t in Set.Ioi (0 : ℝ),
          (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t| :=
        mul_le_mul_of_nonneg_right hπ1 (abs_nonneg _)
    _ ≤ 2 * L * (ρ + ‖x‖) := by rw [one_mul]; exact h1

/-- The modified pieces are Lipschitz with a constant uniform in `k`. -/
theorem abs_omegaTildePiece_sub_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (z₁ z₂ : ℝᵈ) :
    |omegaTildePiece (d := d) k w z₁ - omegaTildePiece (d := d) k w z₂|
      ≤ Creg * tildeConst d * ‖z₁ - z₂‖ := by
  have hcd : ContDiff ℝ 1 (omegaTildePiece (d := d) k w) :=
    (contDiff_omegaTildePiece k hw hk1).of_le (by norm_num)
  have hdiff : Differentiable ℝ (omegaTildePiece (d := d) k w) := hcd.differentiable (by norm_num)
  have h2 : ∀ z, ‖fderiv ℝ (omegaTildePiece (d := d) k w) z‖ ≤ Creg * tildeConst d := by
    intro z
    have h := norm_iteratedFDeriv_omegaTildePiece_le (d := d) hd k 1 (by norm_num) hk1 hw
      hwzero hCreg hwbound z
    rw [norm_iteratedFDeriv_one] at h
    simpa using h
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := omegaTildePiece (d := d) k w) (C := Creg * tildeConst d) (s := Set.univ)
    (fun z _ => hdiff z) (fun z _ => h2 z) convex_univ (Set.mem_univ z₁) (Set.mem_univ z₂)
  rw [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] at hmain
  exact hmain

/-- **Regime 2 for the modified pieces**: the crude bound with the constants of §4. -/
lemma abs_hilbertLine_omegaTildePiece_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    |hilbertLine (omegaTildePiece (d := d) k w) x y|
      ≤ 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ((2 : ℝ) ^ (k + 1) + ‖x‖) := by
  have hL : (0 : ℝ) ≤ Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ)) := by
    have := tildeConst_nonneg d
    positivity
  have hρ : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by positivity
  refine abs_hilbertLine_le _ x y hy hL hρ ?_ ?_
  · intro z₁ z₂
    have h2b : ∀ z : ℝᵈ, ‖iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) z‖
        ≤ Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ)) := by
      intro z
      have h := norm_iteratedFDeriv_omegaTildePiece_le (d := d) hd k 2 (by norm_num) hk1 hw
        hwzero hCreg hwbound z
      refine le_trans h (le_of_eq ?_)
      congr 1
      push_cast
      ring
    exact Commons.Analysis.Calculus.norm_fderiv_sub_le hL
      ((contDiff_omegaTildePiece k hw hk1).of_le (by norm_num)) h2b z₂ z₁
  · intro z hz
    have hev := omegaTildePiece_eventuallyEq_zero_of_norm_gt k w hz
    have h1 : HasFDerivAt (omegaTildePiece (d := d) k w) (0 : ℝᵈ →L[ℝ] ℝ) z :=
      (hasFDerivAt_const (x := z) (c := (0 : ℝ))).congr_of_eventuallyEq hev
    exact h1.fderiv

/-- **Regime 2, with the bound evaluated**: if `‖x‖ ≤ 2^{k}` (which holds for points of the line
once `k ≥ m₀`), the crude bound is at most `6 C_reg C̃`. -/
lemma abs_hilbertLine_omegaTildePiece_le_const (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x y : ℝᵈ) (hy : ‖y‖ = 1) (hx : ‖x‖ ≤ (2 : ℝ) ^ (k + 1)) :
    |hilbertLine (omegaTildePiece (d := d) k w) x y| ≤ 8 * (Creg * tildeConst d) := by
  have h := abs_hilbertLine_omegaTildePiece_le (d := d) hd k hk1 hw hwzero hCreg hwbound x y hy
  have hk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : (2 : ℝ) ^ (k + 1) + ‖x‖ ≤ 2 * (2 : ℝ) ^ (k + 1) := by linarith
  refine le_trans h ?_
  have h2 : 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ((2 : ℝ) ^ (k + 1) + ‖x‖)
      ≤ 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * (2 * (2 : ℝ) ^ (k + 1)) :=
    mul_le_mul_of_nonneg_left h1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (mul_nonneg hCreg.le
        (tildeConst_nonneg d)) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)))
  refine le_trans h2 (le_of_eq ?_)
  have hR : (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ k = 1 := by
    rw [← inv_two_pow]
    exact inv_mul_cancel₀ (by positivity : ((2 : ℝ) ^ k) ≠ 0)
  calc 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * (2 * (2 : ℝ) ^ (k + 1))
      = 8 * (Creg * tildeConst d) * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ k) := by
        rw [pow_succ]; ring
    _ = 8 * (Creg * tildeConst d) := by rw [hR, mul_one]

/-! ## Regime 3: integration by parts -/

/-- **Regime 3.**  If `f` is `C³`, supported in the ball of radius `ρ` and vanishes on the
segment `{x₀ + t y : |t| ≤ δ}`, then the Hilbert transform of the derivative is the integral of
`f` against `t^{-2}`:

  `H[∂_y f](x₀) = (1/π) ∫_ℝ f(x₀ + t y)/t² dt`.

This is Lemma `lem:second_deriv_spherical_prj`'s companion identity, proved by integration by
parts at the level of the one-dimensional function `t ↦ f(x₀ + t y)`. -/
theorem abs_hilbertLine_le_integral (f : ℝᵈ → ℝ) (hdiff : ContDiff ℝ 3 f) (x₀ y : ℝᵈ)
    (hy : ‖y‖ = 1) {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hsupp : ∀ z : ℝᵈ, ρ < ‖z‖ → f z = 0)
    (hzero : ∀ t : ℝ, |t| ≤ δ → f (x₀ + t • y) = 0) :
    |hilbertLine f x₀ y| ≤ (1 / π) * ∫ t : ℝ, |f (x₀ + t • y)| / t ^ 2 := by
  set fl : ℝ → ℝ := fun t => f (x₀ + t • y) with hfl
  have hline : ContDiff ℝ 3 (fun t : ℝ => x₀ + t • y) := by fun_prop
  have hcd : ContDiff ℝ 2 fl := (hdiff.comp hline).of_le (by norm_num)
  have hcs : HasCompactSupport fl := by
    have hb : ∀ t : ℝ, ρ + ‖x₀‖ < |t| → fl t = 0 := by
      intro t ht
      refine hsupp _ ?_
      have h1 : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
      have h2 : ρ < ‖x₀ + t • y‖ := by
        have h3 : ‖t • y‖ = ‖(x₀ + t • y) - x₀‖ := by rw [add_sub_cancel_left]
        have h4 : ‖(x₀ + t • y) - x₀‖ ≤ ‖x₀ + t • y‖ + ‖x₀‖ := norm_sub_le _ _
        rw [← h3, h1] at h4
        linarith
      exact h2
    have hsub : tsupport fl ⊆ Set.Icc (-(ρ + ‖x₀‖)) (ρ + ‖x₀‖) := by
      rw [tsupport]
      refine closure_minimal ?_ isClosed_Icc
      intro t ht
      rw [Function.mem_support] at ht
      exact Set.mem_Icc.mpr (abs_le.mp (le_of_not_gt fun h => ht (hb t h)))
    exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub
  have h0 : ∀ t : ℝ, |t| ≤ δ → fl t = 0 := hzero
  have hkey := Commons.Analysis.Calculus.abs_integral_Ioi_slope_le_integral_abs_div_sq hδ hcd hcs h0
  have hrel : hilbertLine f x₀ y
      = (1 / π) * ∫ t in Set.Ioi (0 : ℝ), (deriv fl t - deriv fl (-t)) / t := by
    rw [hilbertLine_def]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    have hxy : x₀ - t • y = x₀ + (-t) • y := by rw [sub_eq_add_neg, neg_smul]
    rw [hxy, ← deriv_comp_line (hdiff.differentiable (by norm_num)) x₀ y t,
      ← deriv_comp_line (hdiff.differentiable (by norm_num)) x₀ y (-t)]
  rw [hrel, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)


/-! ## Regime 3, continued: the ray integrals -/

/-- The ray restriction `t ↦ ω̃_k(t • y)` is compactly supported. -/
lemma hasCompactSupport_omegaTildePiece_ray (k : ℕ) (w : ℝᵈ → ℝ) (y : ℝᵈ) (hy : ‖y‖ = 1) :
    HasCompactSupport (fun t : ℝ => omegaTildePiece (d := d) k w (t • y)) := by
  have hsub : tsupport (fun t : ℝ => omegaTildePiece (d := d) k w (t • y))
      ⊆ Set.Icc (-((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ (k + 1)) := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    rw [Function.mem_support] at ht
    have hnorm : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
    refine Set.mem_Icc.mpr (abs_le.mp (le_of_not_gt fun h => ht ?_))
    refine omegaTildePiece_eq_zero_of_norm_ge k w ?_
    rw [hnorm]; exact le_of_lt h
  exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub

/-- The ray restriction vanishes on `[-1,1]` when `k ≥ 2`. -/
lemma omegaTildePiece_ray_eq_zero_small (k : ℕ) (hk2 : 2 ≤ k) (w : ℝᵈ → ℝ) (y : ℝᵈ)
    (hy : ‖y‖ = 1) {t : ℝ} (ht : |t| ≤ 1) : omegaTildePiece (d := d) k w (t • y) = 0 := by
  have hk1 : 1 ≤ k := by omega
  refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
  have hnorm : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
  rw [hnorm]
  calc |t| ≤ 1 := ht
    _ ≤ (2 : ℝ) ^ (k - 1) := by
        calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
          _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- **The integral of `|ω̃_k|` against `t^{-2}` along a ray is `|q_k|`.** -/
theorem setIntegral_Ioi_abs_omegaTildePiece_div_sq (k : ℕ) (hk2 : 2 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwk : ∀ x, omegaTildePiece (d := d) k w x ≤ 0)
    (y : ℝᵈ) (hy : ‖y‖ = 1) :
    (∫ t in Set.Ioi (0 : ℝ), |omegaTildePiece (d := d) k w (t • y)| / t ^ 2) = |qk k w| := by
  have hk1 : 1 ≤ k := by omega
  set fl : ℝ → ℝ := fun t => omegaTildePiece (d := d) k w (t • y) with hfl
  have hfl_le : ∀ t, fl t ≤ 0 := fun t => hwk _
  have h1 : (∫ t in Set.Ioi (0 : ℝ), fl t / t ^ 2) = qk k w := by
    have h := sphProj_omegaTilde k hk1 hw.continuous hy
    simp only [sphProj] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show omegaTildePiece (d := d) k w (t • y) / t ^ 2 = omegaTilde k w (t • y) * (t ^ 2)⁻¹
    rw [omegaTildePiece_of_le k w hk2]
    ring
  have h2 : (∫ t in Set.Ioi (0 : ℝ), |fl t| / t ^ 2)
      = -(∫ t in Set.Ioi (0 : ℝ), fl t / t ^ 2) := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [abs_of_nonpos (hfl_le t)]
    ring
  have h3 : (0 : ℝ) ≤ ∫ t in Set.Ioi (0 : ℝ), |fl t| / t ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => div_nonneg (abs_nonneg _) (by positivity))
  have hq : qk k w ≤ 0 := by linarith [h1, h2, h3]
  rw [h2, h1, abs_of_nonpos hq]

/-- **The integral of `|ω̃_k|` against `t^{-2}` over the whole line is `2|q_k|`.** -/
theorem integral_abs_omegaTildePiece_div_sq (k : ℕ) (hk2 : 2 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwk : ∀ x, omegaTildePiece (d := d) k w x ≤ 0)
    (y : ℝᵈ) (hy : ‖y‖ = 1) :
    (∫ t : ℝ, |omegaTildePiece (d := d) k w (t • y)| / t ^ 2) = 2 * |qk k w| := by
  have hk1 : 1 ≤ k := by omega
  set fl : ℝ → ℝ := fun t => omegaTildePiece (d := d) k w (t • y) with hfl
  have hcont : Continuous fl :=
    (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
  have hcs : HasCompactSupport fl := hasCompactSupport_omegaTildePiece_ray k w y hy
  have hzero : ∀ t : ℝ, |t| ≤ 1 → fl t = 0 := fun t ht =>
    omegaTildePiece_ray_eq_zero_small k hk2 w y hy ht
  have hint : Integrable (fun t : ℝ => fl t / t ^ 2) :=
    Commons.Analysis.Calculus.integrable_div_sq_of_continuous_hasCompactSupport hcont hcs hzero
  have hint' : Integrable (fun t : ℝ => |fl t| / t ^ 2) := by
    refine (hint.abs).congr ?_
    filter_upwards with t
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)]
  have hneg : (∫ t in Set.Iic (0 : ℝ), |fl t| / t ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ), |omegaTildePiece (d := d) k w (t • (-y))| / t ^ 2 := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun t : ℝ => |fl t| / t ^ 2)
    rw [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show |omegaTildePiece (d := d) k w ((-t) • y)| / (-t) ^ 2
      = |omegaTildePiece (d := d) k w (t • (-y))| / t ^ 2
    rw [show (-t) • y = t • (-y) from by rw [neg_smul, smul_neg]]
    ring_nf
  rw [← integral_add_compl (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      hint', Set.compl_Ioi,
    setIntegral_Ioi_abs_omegaTildePiece_div_sq k hk2 hw hwk y hy, hneg,
    setIntegral_Ioi_abs_omegaTildePiece_div_sq k hk2 hw hwk (-y) (by simpa using hy)]
  ring

/-! ## Regime 3, concluded: the shifted integral and the main estimate -/

/-- **The shifted ray integral.**  For `k ≥ 2` and `δ ≥ 1` such that the line `{x₀ + t y}`
stays inside `{‖z‖ ≤ 2^{k-1}}` for `|t| ≤ δ`, the integral of `|ω̃_k|` against `t^{-2}` along the
shifted line is bounded by `2|q_k|` plus the translation error `C_reg C̃ ‖x₀‖ (2/δ)`. -/
theorem integral_abs_line_div_sq_le (hd : 1 ≤ d) (k : ℕ) (hk2 : 2 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ x, omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x₀ y : ℝᵈ) (hy : ‖y‖ = 1) {δ : ℝ} (hδ1 : 1 ≤ δ)
    (hsup : ‖x₀‖ + δ ≤ (2 : ℝ) ^ (k - 1)) :
    (∫ t : ℝ, |omegaTildePiece (d := d) k w (x₀ + t • y)| / t ^ 2)
      ≤ 2 * |qk k w| + Creg * tildeConst d * ‖x₀‖ * (2 / δ) := by
  have hδ : (0 : ℝ) < δ := lt_of_lt_of_le one_pos hδ1
  have hk1 : 1 ≤ k := by omega
  set fl₁ : ℝ → ℝ := fun t => omegaTildePiece (d := d) k w (t • y) with hfl₁
  set fl₂ : ℝ → ℝ := fun t => omegaTildePiece (d := d) k w (x₀ + t • y) with hfl₂
  set M : ℝ := Creg * tildeConst d * ‖x₀‖ with hM
  set s : Set ℝ := {t : ℝ | δ ≤ |t|} with hs
  have hs_meas : MeasurableSet s :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  -- the pointwise comparison
  have hpoint : ∀ t : ℝ,
      |fl₂ t| / t ^ 2 ≤ |fl₁ t| / t ^ 2 + M * s.indicator (fun t => (t ^ 2)⁻¹) t := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht]
      have hδle : δ ≤ |t| := ht
      have htne : t ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hδle
        linarith
      have ht2 : (0 : ℝ) < t ^ 2 := by positivity
      have hdiff : |fl₂ t - fl₁ t| ≤ M := by
        have h := abs_omegaTildePiece_sub_le (d := d) hd k hk1 hw hwzero hCreg hwbound
          (x₀ + t • y) (t • y)
        have hsub : ‖x₀ + t • y - t • y‖ = ‖x₀‖ := by rw [add_sub_cancel_right]
        rw [hsub, ← hM] at h
        exact h
      have htri : |fl₂ t| ≤ |fl₁ t| + M := by
        calc |fl₂ t| = |(fl₂ t - fl₁ t) + fl₁ t| := by ring_nf
          _ ≤ |fl₂ t - fl₁ t| + |fl₁ t| := abs_add_le _ _
          _ ≤ M + |fl₁ t| := by linarith
          _ = |fl₁ t| + M := by ring
      calc |fl₂ t| / t ^ 2 ≤ (|fl₁ t| + M) / t ^ 2 := div_le_div_of_nonneg_right htri ht2.le
        _ = |fl₁ t| / t ^ 2 + M * (t ^ 2)⁻¹ := by rw [add_div]; ring
    · rw [Set.indicator_of_notMem ht, mul_zero, add_zero]
      have hlt : |t| < δ := lt_of_not_ge (fun h => ht h)
      have hzero : fl₂ t = 0 := by
        rw [hfl₂]
        refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
        have h3 : ‖x₀ + t • y‖ ≤ ‖x₀‖ + |t| := by
          calc ‖x₀ + t • y‖ ≤ ‖x₀‖ + ‖t • y‖ := norm_add_le _ _
            _ = ‖x₀‖ + |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
        linarith
      rw [hzero, abs_zero, zero_div]
      exact div_nonneg (abs_nonneg _) (by positivity)
  -- integrability
  have hcont1 : Continuous fl₁ :=
    (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
  have hcs1 : HasCompactSupport fl₁ := hasCompactSupport_omegaTildePiece_ray k w y hy
  have hzero1 : ∀ t : ℝ, |t| ≤ 1 → fl₁ t = 0 := fun t ht =>
    omegaTildePiece_ray_eq_zero_small k hk2 w y hy ht
  have hint1 : Integrable (fun t : ℝ => |fl₁ t| / t ^ 2) := by
    have h := Commons.Analysis.Calculus.integrable_div_sq_of_continuous_hasCompactSupport
      hcont1 hcs1 hzero1
    refine h.abs.congr ?_
    filter_upwards with t
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)]
  have hcont2 : Continuous fl₂ :=
    (contDiff_omegaTildePiece k hw hk1).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hcs2 : HasCompactSupport fl₂ := by
    have hsub : tsupport fl₂ ⊆
        Set.Icc (-((2 : ℝ) ^ (k + 1) + ‖x₀‖)) ((2 : ℝ) ^ (k + 1) + ‖x₀‖) := by
      rw [tsupport]
      refine closure_minimal ?_ isClosed_Icc
      intro t ht
      rw [Function.mem_support] at ht
      rw [hfl₂] at ht
      have hle : ‖x₀ + t • y‖ ≤ (2 : ℝ) ^ (k + 1) := by
        by_contra hc
        push Not at hc
        exact ht (omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt hc))
      have hb : |t| ≤ (2 : ℝ) ^ (k + 1) + ‖x₀‖ := by
        have h3 : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
        calc |t| = ‖t • y‖ := h3.symm
          _ = ‖(x₀ + t • y) - x₀‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖x₀ + t • y‖ + ‖x₀‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      exact Set.mem_Icc.mpr (abs_le.mp hb)
    exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub
  have hzero2 : ∀ t : ℝ, |t| ≤ 1 → fl₂ t = 0 := by
    intro t ht
    rw [hfl₂]
    refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
    have h3 : ‖x₀ + t • y‖ ≤ ‖x₀‖ + |t| := by
      calc ‖x₀ + t • y‖ ≤ ‖x₀‖ + ‖t • y‖ := norm_add_le _ _
        _ = ‖x₀‖ + |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
    linarith
  have hint2 : Integrable (fun t : ℝ => |fl₂ t| / t ^ 2) := by
    have h := Commons.Analysis.Calculus.integrable_div_sq_of_continuous_hasCompactSupport
      hcont2 hcs2 hzero2
    refine h.abs.congr ?_
    filter_upwards with t
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)]
  have hInt_ind : Integrable (fun t : ℝ => s.indicator (fun t => (t ^ 2)⁻¹) t) := by
    by_contra h
    have h0 : (∫ t : ℝ, s.indicator (fun t => (t ^ 2)⁻¹) t) = 0 := integral_undef h
    have hne : (∫ t : ℝ, s.indicator (fun t => (t ^ 2)⁻¹) t) ≠ 0 := by
      rw [hs, Commons.MeasureTheory.Integral.integral_indicator_inv_sq_abs_ge hδ]
      exact mul_ne_zero two_ne_zero (inv_ne_zero (ne_of_gt hδ))
    exact hne h0
  have hIntM : Integrable (fun t : ℝ => M * s.indicator (fun t => (t ^ 2)⁻¹) t) :=
    hInt_ind.const_mul M
  have hIntR : Integrable (fun t : ℝ =>
      |fl₁ t| / t ^ 2 + M * s.indicator (fun t => (t ^ 2)⁻¹) t) := hint1.add hIntM
  have hmono := integral_mono hint2 hIntR hpoint
  rw [integral_add hint1 hIntM, integral_const_mul,
    Commons.MeasureTheory.Integral.integral_indicator_inv_sq_abs_ge hδ] at hmono
  refine le_trans hmono ?_
  rw [integral_abs_omegaTildePiece_div_sq k hk2 hw hwk y hy]
  have hMnn : 0 ≤ M := by
    rw [hM]; have := tildeConst_nonneg d; positivity
  have h2δ : 2 * δ⁻¹ = 2 / δ := by rw [div_eq_mul_inv]
  rw [h2δ]

/-- Arithmetic: `m₀ + 7 ≤ k` and `r ≤ 2^{m₀+1}` give `r + 2^{k-2} ≤ 2^{k-1}`. -/
lemma pow_two_arith {m₀ k : ℕ} (hmk : m₀ + 7 ≤ k) {r : ℝ} (hr : r ≤ (2 : ℝ) ^ (m₀ + 1)) :
    r + (2 : ℝ) ^ (k - 2) ≤ (2 : ℝ) ^ (k - 1) := by
  have h1 : (2 : ℝ) ^ (m₀ + 1) ≤ (2 : ℝ) ^ (k - 6) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (2 : ℝ) ^ (k - 2) = (2 : ℝ) ^ (k - 6) * 16 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 from by norm_num, ← pow_add]
    congr 1
    omega
  have h5 : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ (k - 6) * 32 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ 5 from by norm_num, ← pow_add]
    congr 1
    omega
  rw [h4, h5]
  nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (k - 6) by positivity]

/-- Arithmetic: `2·(2^{k-2})⁻¹ = 8·(2^k)⁻¹` for `k ≥ 2`. -/
lemma inv_pow_two_sub_two (k : ℕ) (hk : 2 ≤ k) :
    2 * ((2 : ℝ) ^ (k - 2))⁻¹ = 8 * ((2 : ℝ) ^ k)⁻¹ := by
  have h : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 2) * 4 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_add]
    congr 1
    omega
  rw [h, mul_inv_rev]
  norm_num
  ring

/-- **`eq:estimate_H_tilde_omega_k_sum` of Cohen's §4.**  For the line `{x₀ + t ŷ}` (with `x₀` the
closest point to the origin) the Hilbert transforms of the derivatives of the modified pieces sum
up to at most `57 C_reg C̃ + 256 C_gr`:

  `∑_{k=1}^K |H[ω̃_k|_ℓ'](x₀)| ≤ 57 C_reg C̃ + 256 C_gr`,

uniformly in `K`. -/
theorem sum_abs_hilbertLine_le (hd : 1 ≤ d) {K : ℕ} {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    (x₀ y : ℝᵈ) (hy : ‖y‖ = 1) (hperp₀ : inner ℝ x₀ y = 0) :
    (∑ k ∈ Finset.Icc 1 K, |hilbertLine (omegaTildePiece (d := d) k w) x₀ y|)
      ≤ 57 * (Creg * tildeConst d) + 256 * Cgr := by
  obtain ⟨hint, hgrle⟩ := hgrowth
  have hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro x
    have h := hwbound 0 (by norm_num) x
    simpa [norm_iteratedFDeriv_zero] using h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖x₀‖ ≤ (2 : ℝ) ^ (m + 1) := by
    obtain ⟨n, hn⟩ := exists_pow_gt_norm (d := d) x₀
    refine ⟨n, le_of_lt (lt_of_lt_of_le hn ?_)⟩
    rw [pow_succ]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
  have hex : ∃ m : ℕ, ‖x₀‖ ≤ (2 : ℝ) ^ (m + 1) := ⟨m, hm⟩
  set m₀ := Nat.find hex with hm₀def
  have hm₀ : ‖x₀‖ ≤ (2 : ℝ) ^ (m₀ + 1) := Nat.find_spec hex
  have hm₀min : ∀ k : ℕ, k < m₀ → (2 : ℝ) ^ (k + 1) < ‖x₀‖ := by
    intro k hk
    refine lt_of_not_ge fun hc => ?_
    exact absurd (Nat.find_min' hex hc) (not_le.mpr hk)
  set f : ℕ → ℝ := fun k => |hilbertLine (omegaTildePiece (d := d) k w) x₀ y| with hf
  set SA := (Finset.Icc 1 K).filter (fun k => k < m₀) with hSA
  set SB := ((Finset.Icc 1 K).filter (fun k => ¬ k < m₀)).filter (fun k => k ≤ m₀ + 6) with hSB
  set SC := ((Finset.Icc 1 K).filter (fun k => ¬ k < m₀)).filter (fun k => ¬ k ≤ m₀ + 6)
    with hSC
  -- regime A: the transform vanishes
  have hA : (∑ k ∈ SA, f k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hSA, Finset.mem_filter] at hk
    show |hilbertLine (omegaTildePiece (d := d) k w) x₀ y| = 0
    rw [hilbertLine_omegaTildePiece_eq_zero k w x₀ y hy hperp₀ (hm₀min k hk.2), abs_zero]
  -- regime B: the crude bound
  have hB : (∑ k ∈ SB, f k) ≤ 56 * (Creg * tildeConst d) := by
    have hcard : SB.card ≤ 7 := by
      have hsub : SB ⊆ Finset.Icc m₀ (m₀ + 6) := by
        intro k hk
        rw [hSB, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hk
        obtain ⟨⟨⟨hk1, hkK⟩, hkm⟩, hk6⟩ := hk
        exact Finset.mem_Icc.mpr ⟨not_lt.mp hkm, hk6⟩
      have h7 : (Finset.Icc m₀ (m₀ + 6)).card = 7 := by
        rw [Nat.card_Icc]; omega
      calc SB.card ≤ (Finset.Icc m₀ (m₀ + 6)).card := Finset.card_le_card hsub
        _ = 7 := h7
    have hterm : ∀ k ∈ SB, f k ≤ 8 * (Creg * tildeConst d) := by
      intro k hk
      rw [hSB, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨⟨hk1, hkK⟩, hkm⟩, hk6⟩ := hk
      have hk1' : 1 ≤ k := hk1
      refine abs_hilbertLine_omegaTildePiece_le_const (d := d) hd k hk1' hw hwzero hCreg hwbound
        x₀ y hy ?_
      calc ‖x₀‖ ≤ (2 : ℝ) ^ (m₀ + 1) := hm₀
        _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (∑ k ∈ SB, f k) ≤ ∑ k ∈ SB, 8 * (Creg * tildeConst d) := Finset.sum_le_sum hterm
      _ = 8 * (Creg * tildeConst d) * SB.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 8 * (Creg * tildeConst d) * 7 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num)
            (mul_nonneg hCreg.le (tildeConst_nonneg d)))
          exact_mod_cast hcard
      _ = 56 * (Creg * tildeConst d) := by ring
  -- regime C: integration by parts
  have hC : (∑ k ∈ SC, f k)
      ≤ (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
        + Creg * tildeConst d := by
    have hterm : ∀ k ∈ SC, f k ≤ (1 / π) * (2 * |qk k w|
        + Creg * tildeConst d * ‖x₀‖ * (8 * ((2 : ℝ) ^ k)⁻¹)) := by
      intro k hk
      rw [hSC, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨⟨hk1, hkK⟩, hkm⟩, hk6⟩ := hk
      have hk7 : m₀ + 7 ≤ k := by omega
      have hk2 : 2 ≤ k := by omega
      have hk1' : 1 ≤ k := by omega
      have hsup' := pow_two_arith hk7 hm₀
      -- the integration-by-parts bound
      have hstep1 : f k ≤ (1 / π) *
          ∫ t : ℝ, |omegaTildePiece (d := d) k w (x₀ + t • y)| / t ^ 2 := by
        rw [hf]
        refine abs_hilbertLine_le_integral (omegaTildePiece (d := d) k w)
          (contDiff_omegaTildePiece k hw hk1') x₀ y hy (ρ := (2 : ℝ) ^ (k + 1))
          (δ := (2 : ℝ) ^ (k - 2)) (by positivity) (by positivity) ?_ ?_
        · intro z hz
          exact omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt hz)
        · intro t ht
          refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1' w ?_
          have h3 : ‖x₀ + t • y‖ ≤ ‖x₀‖ + |t| := by
            calc ‖x₀ + t • y‖ ≤ ‖x₀‖ + ‖t • y‖ := norm_add_le _ _
              _ = ‖x₀‖ + |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
          linarith
      have hδ1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 2) := by
        calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
          _ ≤ (2 : ℝ) ^ (k - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hstep2 := integral_abs_line_div_sq_le (d := d) hd k hk2 hw hwzero (hwk k) hCreg
        hwbound x₀ y hy (δ := (2 : ℝ) ^ (k - 2)) hδ1 hsup'
      calc f k ≤ (1 / π) * ∫ t : ℝ, |omegaTildePiece (d := d) k w (x₀ + t • y)| / t ^ 2 :=
            hstep1
        _ ≤ (1 / π) * (2 * |qk k w| + Creg * tildeConst d * ‖x₀‖ * (2 / (2 : ℝ) ^ (k - 2))) :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = (1 / π) * (2 * |qk k w|
              + Creg * tildeConst d * ‖x₀‖ * (8 * ((2 : ℝ) ^ k)⁻¹)) := by
            rw [show (2 : ℝ) / (2 : ℝ) ^ (k - 2) = 8 * ((2 : ℝ) ^ k)⁻¹ from by
              rw [div_eq_mul_inv]
              exact inv_pow_two_sub_two k hk2]
    -- sum the two parts
    have hsum1 : (∑ k ∈ SC, (1 / π) * (2 * |qk k w|)) = (2 / π) * ∑ k ∈ SC, |qk k w| := by
      rw [show (2 / π) * (∑ k ∈ SC, |qk k w|) = ∑ k ∈ SC, (2 / π) * |qk k w| from by
        rw [Finset.mul_sum]]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hsum2 : (∑ k ∈ SC, (1 / π) * (Creg * tildeConst d * ‖x₀‖ * (8 * ((2 : ℝ) ^ k)⁻¹)))
        = (8 / π * (Creg * tildeConst d * ‖x₀‖)) * ∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹ := by
      rw [show (8 / π * (Creg * tildeConst d * ‖x₀‖)) * (∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹)
          = ∑ k ∈ SC, (8 / π * (Creg * tildeConst d * ‖x₀‖)) * ((2 : ℝ) ^ k)⁻¹ from by
        rw [Finset.mul_sum]]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hSCsub : SC ⊆ Finset.Icc (m₀ + 7) K := by
      intro k hk
      rw [hSC, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨⟨hk1, hkK⟩, hkm⟩, hk6⟩ := hk
      exact Finset.mem_Icc.mpr ⟨by omega, hkK⟩
    have hsum3 : (∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹) ≤ 2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹ := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSCsub (fun k _ _ => by positivity)) ?_
      exact sum_Icc_inv_pow_two_le (m₀ + 7) K
    have hsum4 : (∑ k ∈ SC, |qk k w|) ≤ 128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) := by
      have hsub : SC ⊆ Finset.Icc 1 K := by
        intro k hk
        rw [hSC, Finset.mem_filter, Finset.mem_filter] at hk
        exact hk.1.1
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
        (sum_abs_qk_le_growth (d := d) hd hw.continuous hwnonpos hCreg.le hreg hint)
    have hCnn : (0 : ℝ) ≤ Creg * tildeConst d * ‖x₀‖ := by
      have := tildeConst_nonneg d
      positivity
    have hkey : 8 / π * (Creg * tildeConst d * ‖x₀‖) * (2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹)
        ≤ Creg * tildeConst d := by
      have hpow : (2 : ℝ) ^ (m₀ + 7) = (2 : ℝ) ^ (m₀ + 1) * 64 := by
        rw [show m₀ + 7 = (m₀ + 1) + 6 from by omega, pow_add]
        norm_num
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (m₀ + 1) := by positivity
      have h2 : ‖x₀‖ * ((2 : ℝ) ^ (m₀ + 7))⁻¹ ≤ (64 : ℝ)⁻¹ := by
        have h3 : ‖x₀‖ * ((2 : ℝ) ^ (m₀ + 1))⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hpos]
          exact hm₀
        rw [hpow, mul_inv_rev]
        calc ‖x₀‖ * ((64 : ℝ)⁻¹ * ((2 : ℝ) ^ (m₀ + 1))⁻¹)
            = (‖x₀‖ * ((2 : ℝ) ^ (m₀ + 1))⁻¹) * (64 : ℝ)⁻¹ := by ring
          _ ≤ 1 * (64 : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h3 (by norm_num)
          _ = (64 : ℝ)⁻¹ := by ring
      have hCT : (0 : ℝ) ≤ Creg * tildeConst d := mul_nonneg hCreg.le (tildeConst_nonneg d)
      calc 8 / π * (Creg * tildeConst d * ‖x₀‖) * (2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹)
          = (16 / π) * (Creg * tildeConst d) * (‖x₀‖ * ((2 : ℝ) ^ (m₀ + 7))⁻¹) := by ring
        _ ≤ (16 / π) * (Creg * tildeConst d) * (64 : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (1 / (4 * π)) * (Creg * tildeConst d) := by ring
        _ ≤ 1 * (Creg * tildeConst d) := by
            refine mul_le_mul_of_nonneg_right ?_ hCT
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * π)]
            nlinarith [Real.pi_gt_three]
        _ = Creg * tildeConst d := by ring
    calc (∑ k ∈ SC, f k)
        ≤ ∑ k ∈ SC, (1 / π) * (2 * |qk k w|
            + Creg * tildeConst d * ‖x₀‖ * (8 * ((2 : ℝ) ^ k)⁻¹)) := Finset.sum_le_sum hterm
      _ = (2 / π) * (∑ k ∈ SC, |qk k w|)
            + (8 / π * (Creg * tildeConst d * ‖x₀‖)) * ∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹ := by
          rw [show (∑ k ∈ SC, (1 / π) * (2 * |qk k w|
                + Creg * tildeConst d * ‖x₀‖ * (8 * ((2 : ℝ) ^ k)⁻¹)))
              = ∑ k ∈ SC, ((1 / π) * (2 * |qk k w|)
                  + (1 / π) * (Creg * tildeConst d * ‖x₀‖ * (8 * ((2 : ℝ) ^ k)⁻¹))) from
            Finset.sum_congr rfl (fun k _ => by ring)]
          rw [Finset.sum_add_distrib, hsum1, hsum2]
      _ ≤ (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
            + (8 / π * (Creg * tildeConst d * ‖x₀‖)) * (2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hsum4 (by positivity)
          · exact mul_le_mul_of_nonneg_left hsum3 (by positivity)
      _ ≤ (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
            + Creg * tildeConst d := add_le_add le_rfl hkey
  -- assemble
  have hsplit1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) (fun k => k < m₀) f
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 K).filter (fun k => ¬ k < m₀)) (fun k => k ≤ m₀ + 6) f
  rw [← hsplit1, ← hsplit2, hA, zero_add]
  refine le_trans (add_le_add hB hC) ?_
  have hQ : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr := by
    rw [← growthFunctional_eq_Gstar]
    exact hgrle
  have hCgr0 : (0 : ℝ) ≤ Cgr := by
    have h1 : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) :=
      setIntegral_nonneg measurableSet_Ioi (fun r _ => div_nonneg (Gstar_nonneg w r) (by positivity))
    rw [← growthFunctional_eq_Gstar] at h1
    linarith
  have hπ2 : (2 / π * 128 : ℝ) ≤ 256 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < π)]
    nlinarith [Real.pi_gt_three]
  have hbig : (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ 256 * Cgr := by
    have h := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 2 / π * 128)
    calc (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
        = (2 / π * 128) * (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) := by ring
      _ ≤ (2 / π * 128) * Cgr := h
      _ ≤ 256 * Cgr := mul_le_mul_of_nonneg_right hπ2 hCgr0
  linarith [hbig]

end Submission.FUP
