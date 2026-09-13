/-
# Trudinger's classical interior gradient estimate from the interior gradient estimate for `σ₂ = 1`

`Submission.interior_gradient_bound` (`Submission/SmoothGradientMain.lean`) is the interior gradient
estimate for solutions of `σ₂(D²u) = 1` with `Δu > 0`:

  `‖Du 0‖ * r ≤ C (1 + M)^2`  for `|u| ≤ M` on `ball 0 r`, `C` a universal constant.

Trudinger's *classical* interior gradient estimate (Theorem 3.3 of Trudinger--Wang,
*Hessian measures II*; `[T2]`) is the statement with the **oscillation** instead of the sup norm:

  `‖Du(y)‖ * ρ ≤ C (M - m)`  for `m ≤ u ≤ M` on `ball y ρ`.

The two are related by the *parabolic rescaling* `x ↦ y + t x`, `u ↦ (u - m)/t²` with
`t = √(M-m)`: it preserves `σ₂ = 1` (a subgroup of the `a b² = 1` scalings) and normalises the
oscillation to `1`, so that `interior_gradient_bound` applies with `M = 1` and gives
`‖Du(y)‖ ρ ≤ 4 C (M - m)`.

Hence `Submission.InteriorGradientBound` is a *theorem* of the repository, and only Savin's small
perturbation theorem remains as an input.
-/
import Submission.WeightedGradientReduction
import Submission.SmoothGradientMain
import Submission.AffineInvariance

open HessianEstimates
open Laplacian Metric MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- Smoothness of a rescaled function at level `3`. -/
theorem contDiffOn_rescale3 {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {a b : ℝ} {y : ℝ⁴}
    (hu : ContDiffOn ℝ 3 u s) :
    ContDiffOn ℝ 3 (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} := by
  have h1 : ContDiffOn ℝ 3 (fun w => a * u w) s := hu.const_smul a
  have h2 : ContDiffOn ℝ 3 (fun x : ℝ⁴ => b • x + y) {x | b • x + y ∈ s} :=
    (((b • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).contDiff).add contDiff_const).contDiffOn
  exact h1.comp h2 (fun x hx => hx)

/-- **Trudinger's classical interior gradient estimate** in dimension four (Theorem 3.3 of
Trudinger--Wang, *Hessian measures II*), for solutions of `σ₂(D²u) = 1` with `Δu > 0`. -/
theorem interiorGradientBound_holds : InteriorGradientBound := by
  obtain ⟨C, hCpos, hC⟩ := interior_gradient_bound
  refine ⟨4 * C, by positivity, ?_⟩
  intro u s y ρ M m hs hu hσ2 hΔ hρ hsub hb
  have hy_s : y ∈ s := hsub (mem_closedBall_self hρ.le)
  have hmM : m ≤ M := by
    have h := hb y (mem_ball_self hρ)
    linarith [h.1, h.2]
  rcases lt_or_eq_of_le hmM with hlt | heq
  · -- ## the main case: normalise the oscillation by a parabolic rescaling
    set ω : ℝ := M - m with hω
    set t : ℝ := Real.sqrt ω with ht
    set ũ : ℝ⁴ → ℝ := fun x => u x - m with hũ
    set w : ℝ⁴ → ℝ := fun z => (1 / ω) * ũ (t • z + y) with hw
    set S : Set ℝ⁴ := ball (0 : ℝ⁴) (ρ / t) with hS
    set s' : Set ℝ⁴ := {x : ℝ⁴ | t • x + y ∈ s} with hs'
    have hωpos : 0 < ω := by rw [hω]; linarith
    have htpos : 0 < t := by rw [ht]; exact Real.sqrt_pos.mpr hωpos
    have ht2 : t ^ 2 = ω := by rw [ht]; exact Real.sq_sqrt hωpos.le
    have hab : (1 / ω) * t ^ 2 = 1 := by rw [ht2]; field_simp
    have hSval : S = ball (0 : ℝ⁴) (ρ / t) := hS
    have hs'val : s' = {x : ℝ⁴ | t • x + y ∈ s} := hs'
    have hweq : w = fun z : ℝ⁴ => (1 / ω) * ũ (t • z + y) := by funext z; rw [hw]
    have hũeq : ũ = fun x : ℝ⁴ => u x - m := by funext x; rw [hũ]
    have hs'open : IsOpen s' := by
      rw [hs'val]
      exact hs.preimage (((t • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).continuous).add continuous_const)
    have hSsub : S ⊆ s' := by
      intro z hz
      rw [hSval] at hz
      rw [mem_ball, dist_zero_right] at hz
      rw [hs'val]
      simp only [mem_setOf_eq]
      refine hsub ?_
      rw [mem_closedBall, dist_eq_norm]
      have h1 : t • z + y - y = t • z := by rw [add_sub_cancel_right]
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      rw [lt_div_iff₀ htpos] at hz
      linarith
    -- ## the hypotheses for the rescaled function
    have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
    have hu3' : ContDiffOn ℝ 3 ũ s := by
      rw [hũeq]
      exact hu.sub (contDiffOn_const : ContDiffOn ℝ 3 (fun _ : ℝ⁴ => m) s)
    have hu2' : ContDiffOn ℝ 2 ũ s := hu3'.of_le (by norm_num)
    have hcontS : ContDiffOn ℝ 3 w S := by
      rw [hweq]
      exact (contDiffOn_rescale3 (a := 1 / ω) (b := t) (y := y) hu3').mono hSsub
    have hbndS : ∀ z ∈ S, |w z| ≤ 1 := by
      intro z hz
      have hz' : t • z + y ∈ ball y ρ := by
        rw [hSval, mem_ball, dist_zero_right] at hz
        rw [mem_ball, dist_eq_norm]
        have h1 : t • z + y - y = t • z := by rw [add_sub_cancel_right]
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        rw [lt_div_iff₀ htpos] at hz
        linarith
      obtain ⟨hb1, hb2⟩ := hb (t • z + y) hz'
      rw [hweq]
      show |(1 / ω) * ũ (t • z + y)| ≤ 1
      have hxv : ũ (t • z + y) = u (t • z + y) - m := by rw [hũeq]
      rw [hxv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ω)]
      have h1 : 0 ≤ u (t • z + y) - m := by linarith
      have h2 : u (t • z + y) - m ≤ ω := by rw [hω]; linarith
      rw [abs_of_nonneg h1]
      have h3 : (1 / ω) * (u (t • z + y) - m) ≤ (1 / ω) * ω :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (1 / ω) * ω = 1 := by
        rw [one_div]
        exact inv_mul_cancel₀ (ne_of_gt hωpos)
      linarith [h3, h4]
    have hzw_of : ∀ z ∈ S, t • z + y ∈ s := by
      intro z hz
      have h1 := hSsub hz
      rwa [hs'val] at h1
    have hσS : ∀ z ∈ S, σ₂ (H w S z) = 1 := by
      intro z hz
      have hzw : t • z + y ∈ s := hzw_of z hz
      have hzball : z ∈ ball (0 : ℝ⁴) (ρ / t) := by rwa [hSval] at hz
      have h1 : H w S z = H w s' z :=
        H_congr_of_mem_nhds (isOpen_ball.mem_nhds hzball) (hs'open.mem_nhds (hSsub hz))
      rw [h1]
      show σ₂ (H (fun x : ℝ⁴ => (1 / ω) * ũ (t • x + y)) {x : ℝ⁴ | t • x + y ∈ s} z) = 1
      rw [sigma2_rescale (u := ũ) (s := s) (a := 1 / ω) (b := t) (y := y) (z := z)
        hs hu2' hzw hab]
      show σ₂ (H ũ s (t • z + y)) = 1
      rw [hũeq]
      have h2 : H (fun x : ℝ⁴ => u x - m) s (t • z + y) = H u s (t • z + y) := by
        simpa using H_sub_affine (hs.mem_nhds hzw) (hu2.contDiffWithinAt hzw) m 0
      rw [h2]
      exact hσ2 (t • z + y) hzw
    have hΔS : ∀ z ∈ S, 0 < (Δ w) z := by
      intro z hz
      have hzw : t • z + y ∈ s := hzw_of z hz
      rw [hweq]
      rw [laplacian_rescale (u := ũ) (a := 1 / ω) (b := t) (y := y) (z := z)
        ((hu3'.contDiffAt (hs.mem_nhds hzw)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))]
      rw [hab, one_mul]
      have h2 : (Δ ũ) (t • z + y) = (Δ u) (t • z + y) := by
        have h3 : ũ = fun x : ℝ⁴ => u x - (m + (0 : ℝ⁴ →L[ℝ] ℝ) x) := by
          funext x
          rw [hũeq]
          simp
        rw [h3]
        exact laplacian_sub_affine hs hzw hu m 0
      rw [h2]
      exact hΔ (t • z + y) hzw
    -- ## the rescaled estimate
    have hmain := hC w (ρ / t) 1 (by positivity) one_pos hcontS hbndS hσS hΔS
    have hfd : ‖fderiv ℝ w 0‖ = (1 / t) * ‖fderiv ℝ u y‖ := by
      have hdiff : DifferentiableAt ℝ ũ (t • (0:ℝ⁴) + y) := by
        rw [smul_zero, zero_add]
        exact (hu3'.contDiffAt (hs.mem_nhds hy_s)).differentiableAt (by norm_num)
      have h1 : fderiv ℝ w 0 = ((1 / ω) * t) • fderiv ℝ ũ (t • (0:ℝ⁴) + y) := by
        rw [hweq]
        exact fderiv_rescale (a := 1 / ω) (b := t) (y := y) (z := (0:ℝ⁴)) hdiff
      have h2 : fderiv ℝ ũ y = fderiv ℝ u y := by
        rw [hũeq]
        exact fderiv_sub_const m
      rw [h1, smul_zero, zero_add, h2, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / ω), abs_of_pos htpos]
      have h3 : (1 / ω) * t = 1 / t := by
        rw [← ht2]; field_simp
      rw [h3]
    rw [hfd] at hmain
    have h4 : (1 / t) * ‖fderiv ℝ u y‖ * (ρ / t) = (‖fderiv ℝ u y‖ * ρ) / ω := by
      rw [← ht2]
      field_simp
    rw [h4] at hmain
    have h5 : C * (1 + 1) ^ 2 = 4 * C := by ring
    rw [h5] at hmain
    rw [div_le_iff₀ hωpos] at hmain
    rw [hω]
    linarith [hmain]
  · -- ## the degenerate case: `u` is constant on the ball
    have hball : ∀ z ∈ ball y ρ, u z = m := by
      intro z hz
      have h := hb z hz
      rw [← heq] at h
      exact le_antisymm h.2 h.1
    have hev : u =ᶠ[𝓝 y] fun _ => m := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with z hz
      exact hball z hz
    have hfd0 : fderiv ℝ u y = 0 := by
      rw [hev.fderiv_eq]
      exact fderiv_const_apply m
    rw [hfd0, norm_zero, zero_mul, ← heq, sub_self, mul_zero]

end Submission
