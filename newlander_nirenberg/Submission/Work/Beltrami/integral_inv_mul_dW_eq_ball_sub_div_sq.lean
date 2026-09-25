import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.integral_radial_weight_inv_sq_eq_zero
import Submission.Work.Beltrami.dbarW_cauchyT_defs
import Submission.Work.Beltrami.tendsto_cutK_mul
import Submission.Work.Beltrami.dW_kernel
import Submission.Work.Beltrami.tendsto_cutProfile_deriv
import Submission.Work.Beltrami.integrable_mul_cutK
import Submission.Work.Beltrami.contDiff_cutK_smooth
import Submission.Work.Beltrami.dW_limits

namespace Work.Beltrami

open MeasureTheory Filter
open scoped Topology

/-- **The `∂`-derivative of the Cauchy kernel as a principal-value integral.**  For a `C¹` function `H` vanishing off the disc of radius `R > 0`, the singular integral of `∂H` against the Cauchy kernel equals the absolutely convergent integral of `H - H 0` against `w⁻²` over that disc:
`∫ u, u⁻¹ * dW H u = ∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹`.
Here `dW H u = (fderiv ℝ H u 1 - I * fderiv ℝ H u I)/2` is the `∂`-derivative (`Work.Beltrami.dW`). Suggested route: pick a smooth radial cutoff `θ` with `θ = 1` on the support of `H` (so `dW (θ(‖·‖²)) u = deriv θ (‖u‖²) * star u`; the `dW`-analogue of `Work.Beltrami.dbarW_radial`), integrate by parts against `q_ε u = (cutProfile ε (‖u‖²) * θ (‖u‖²)) * u⁻¹` (compactly supported, smooth, `= u⁻¹` near the support of `H`) using `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (Mathlib, with `v = 1` and `v = I`; or copy `Work.Beltrami.integral_mul_dbarW_eq_neg` with the sign of the `I`-term flipped), and let `ε → 0⁺`; the terms where `deriv θ` meets `H` vanish identically (since `deriv θ (‖u‖²) ≠ 0 → R ≤ ‖u‖ → H u = 0`), the `H 0`-parts of the shrinking terms vanish by `Work.Beltrami.integral_radial_weight_inv_sq_eq_zero` (radial weight times `w⁻²`), and the remaining shrinking term is bounded by `O(ε)` on a ball of radius `O(ε)`. -/
theorem integral_inv_mul_dW_eq_ball_sub_div_sq {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hH : ContDiff ℝ 1 H) (hsupp : ∀ u : ℂ, R ≤ ‖u‖ → H u = 0) :
    ∫ u, u⁻¹ * dW H u ∂volume
      = ∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹ ∂volume := by
  have hcomp : HasCompactSupport H := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 R) (fun u hu => by
      rw [Function.mem_support] at hu
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h
      push_neg at h
      exact hu (hsupp u (le_of_lt h)))
  have hK : ∀ ε : ℝ, ContDiff ℝ 1 (cutK ε) := fun ε => contDiff_cutK_smooth ε
  have hck1cont : ∀ ε : ℝ, Continuous (fun u : ℂ => (fderiv ℝ (cutK ε) u) 1) := fun ε =>
    ((hK ε).continuous_fderiv (by simp)).clm_apply continuous_const
  have hckIcont : ∀ ε : ℝ, Continuous (fun u : ℂ => (fderiv ℝ (cutK ε) u) Complex.I) := fun ε =>
    ((hK ε).continuous_fderiv (by simp)).clm_apply continuous_const
  have hH1cont : Continuous (fun u : ℂ => (fderiv ℝ H u) 1) :=
    (hH.continuous_fderiv (by simp)).clm_apply continuous_const
  have hHIcont : Continuous (fun u : ℂ => (fderiv ℝ H u) Complex.I) :=
    (hH.continuous_fderiv (by simp)).clm_apply continuous_const
  have hH1c : HasCompactSupport (fun u : ℂ => (fderiv ℝ H u) 1) :=
    (hcomp.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
  have hHIc : HasCompactSupport (fun u : ℂ => (fderiv ℝ H u) Complex.I) :=
    (hcomp.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (by simp)
  -- uniform bound for `H`
  obtain ⟨MH, hMH⟩ := Continuous.bounded_above_of_compact_support hH.continuous hcomp
  have hMH0 : 0 ≤ MH := le_trans (norm_nonneg _) (hMH 0)
  -- `u ≠ 0` almost everywhere
  have hne : ∀ᵐ u : ℂ ∂(volume : Measure ℂ), u ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  -- integrability of the two summands of `∂(cutK ε)`
  have hIntA : ∀ ε : ℝ, 0 < ε → Integrable (fun u : ℂ =>
      H u * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹))) volume := by
    intro ε hε
    exact (hH.continuous.mul (continuous_deriv_cutProfile_mul_star_inv ε hε))
      |>.integrable_of_hasCompactSupport hcomp.mul_right
  have hIntB : ∀ ε : ℝ, 0 < ε → Integrable (fun u : ℂ =>
      H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹) volume := by
    intro ε hε
    have hvan : ∀ u : ℂ, ‖u‖ < ε → H u * (cutProfile ε (‖u‖^2) : ℂ) * u⁻¹ = 0 := by
      intro u hu
      have h0 : cutProfile ε (‖u‖^2) = 0 :=
        cutProfile_eq_zero_of_le hε (by nlinarith [norm_nonneg u, hu])
      simp [h0]
    have hcont : Continuous (fun u : ℂ => H u * (cutProfile ε (‖u‖^2) : ℂ) * u⁻¹) := by
      rw [continuous_iff_continuousAt]
      intro x
      rcases eq_or_ne x 0 with hx | hx
      · subst hx
        rw [ContinuousAt]
        have hev : (fun u : ℂ => H u * (cutProfile ε (‖u‖^2) : ℂ) * u⁻¹)
            =ᶠ[𝓝 (0:ℂ)] (fun _ => (0:ℂ)) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          exact ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, fun u hu => by
            rw [Metric.mem_ball, dist_zero_right] at hu
            exact hvan u hu⟩
        rw [show H 0 * (cutProfile ε (‖(0:ℂ)‖^2) : ℂ) * (0:ℂ)⁻¹ = 0 by simp]
        exact (tendsto_const_nhds).congr' hev.symm
      · exact (hH.continuous.continuousAt.mul
            (radialCut_contDiff ε 1).continuous.continuousAt).mul
          (continuousAt_id.inv₀ hx)
    have hgc : HasCompactSupport (fun u : ℂ => H u * (cutProfile ε (‖u‖^2) : ℂ) * u⁻¹) :=
      (hcomp.mul_right).mul_right
    refine (integrable_mul_inv _ hcont hgc).congr (Filter.Eventually.of_forall (fun u => ?_))
    show H u * (cutProfile ε (‖u‖^2) : ℂ) * u⁻¹ * u⁻¹ = H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹
    rw [← inv_pow]; ring
  -- integration by parts
  have hIBP : ∀ ε : ℝ, 0 < ε →
      ∫ u, H u * dW (cutK ε) u ∂volume = -∫ u, dW H u * cutK ε u ∂volume := by
    intro ε hε
    refine integral_mul_dW_eq_neg H (cutK ε) (integrable_mul_cutK hH.continuous hcomp ε)
      (integrable_mul_cutK hH1cont hH1c ε) (integrable_mul_cutK hHIcont hHIc ε) ?_ ?_ ?_ ?_
    · exact (hH.continuous.mul (hck1cont ε)).integrable_of_hasCompactSupport hcomp.mul_right
    · exact (hH.continuous.mul (hckIcont ε)).integrable_of_hasCompactSupport hcomp.mul_right
    · exact fun u _ => (hH.differentiable (by simp)) u
    · exact fun u _ => (hK ε).differentiable (by simp) u
  -- the two limits
  have hA : Filter.Tendsto (fun ε : ℝ =>
      ∫ u, H u * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_integral_deriv_cutProfile_mul_star_inv H hH hcomp
  have hB : Filter.Tendsto (fun ε : ℝ => ∫ u, H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹ ∂volume)) :=
    tendsto_integral_mul_cutProfile_inv_sq H hR hH hsupp
  have hL : Filter.Tendsto (fun ε : ℝ => ∫ u, dW H u * cutK ε u ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u, dW H u * u⁻¹ ∂volume)) :=
    tendsto_integral_dW_mul_cutK H hH hcomp
  -- the decomposition of `∫ H * ∂(cutK ε)`
  have hsplit : (fun ε : ℝ => ∫ u, H u * dW (cutK ε) u ∂volume)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun ε : ℝ =>
        (∫ u, H u * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹)))
          - ∫ u, H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← MeasureTheory.integral_sub (hIntA ε hε) (hIntB ε hε)]
    apply integral_congr_ae
    filter_upwards [hne] with u hu
    rw [dW_cutK ε hu]; ring
  have hHdW : Filter.Tendsto (fun ε : ℝ => ∫ u, H u * dW (cutK ε) u ∂volume)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹ ∂volume)) := by
    have h := hA.sub hB
    rw [zero_sub] at h
    exact h.congr' hsplit.symm
  have hIBPev : (fun ε : ℝ => -∫ u, H u * dW (cutK ε) u ∂volume)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun ε : ℝ => ∫ u, dW H u * cutK ε u ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hIBP ε hε]; ring
  have huniq : ∫ u, dW H u * u⁻¹ ∂volume
      = -(-∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹ ∂volume) :=
    tendsto_nhds_unique hL (hHdW.neg.congr' hIBPev)
  calc ∫ u, u⁻¹ * dW H u ∂volume
      = ∫ u, dW H u * u⁻¹ ∂volume := by
        apply integral_congr_ae
        filter_upwards with u
        ring
    _ = ∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹ ∂volume := by
        rw [huniq, neg_neg]
end Work.Beltrami
