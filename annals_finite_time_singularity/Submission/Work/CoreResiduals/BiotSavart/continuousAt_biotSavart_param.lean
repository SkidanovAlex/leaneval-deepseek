import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_ball_integral
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.StabilityFar.Decay.norm_bsK_le_indicator
import Submission.Work.CoreResiduals.BiotSavart.norm_setIntegral_crossL_kf_inter_le
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_integral_crossL_kf_diff
import Submission.Work.CoreResiduals.BiotSavart.integral_crossL_kf_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (crossL kf)

/-- **Continuity of the parametrised Biot–Savart integral.**

For a spacetime vorticity `ω` bounded by `M ≥ 0` on the time window `|t - t₀| < δ`, supported in
the fixed ball `B(0,R)`, with ae-strongly-measurable slices and continuous in `t` at `t₀` for every
fixed `y`, the reconstructed velocity `(x,t) ↦ BS(ω(·,t)) x` is continuous at `(x₀,t₀)`.

Suggested proof: since `hρ : R + ‖x₀‖ + 1 < ρ`, for `x ∈ B(x₀,1)` the field is the integral over
the *fixed* ball `B(0,ρ)` (`biotSavart_ball_integral`):
`(4π)⁻¹ • ∫_{B(0,ρ)} crossL (ω a t) (kf (x-a)) da`.  Split that integral at the fixed centre `x₀`
with radius `Δ > 0`: on `B(0,ρ) ∩ B(x₀,Δ)` its norm is bounded by
`M ∫_{B(x,3Δ/2)} ‖x-a‖⁻² da = 4π M (3Δ/2)`, uniformly in `x ∈ B(x₀,Δ/2)` and in `t`; on the
fixed set `B(0,ρ) \ B(x₀,Δ)` it is continuous at `(x₀,t₀)` by dominated convergence
(`MeasureTheory.continuousWithinAt_of_dominated`) with the *constant* dominating function
`M (Δ/2)⁻²` on the finite-measure set `B(0,ρ)` — for fixed `a` the integrand
`(x,t) ↦ ‖x-a‖⁻³ • (ω a t × (x-a))` is continuous away from `a = x`, and `htcont a` gives
continuity in `t`. -/
theorem continuousAt_biotSavart_param {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ R M ρ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : R + ‖x₀‖ + 1 < ρ)
    (hbdd : ∀ t : ℝ, |t - t₀| < δ → ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hsupp : ∀ t : ℝ, |t - t₀| < δ → ∀ y : Work.LWP.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : ∀ t : ℝ, |t - t₀| < δ →
      MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      Work.LWP.biotSavart (fun y => ω y q.2) q.1) (x₀, t₀) := by
  -- ## Step 1.  On a neighbourhood of `(x₀,t₀)` the field is the integral over the fixed ball.
  have hmem : {q : Work.LWP.R3 × ℝ | ‖q.1 - x₀‖ < 1 ∧ |q.2 - t₀| < δ} ∈ 𝓝 (x₀, t₀) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (x₀, t₀) (lt_min one_pos hδ)) ?_
    intro q hq
    rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at hq
    exact ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hq (min_le_left _ _)),
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hq (min_le_right _ _))⟩
  have hrepr : (fun q : Work.LWP.R3 × ℝ => (4 * Real.pi)⁻¹ •
        ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
      =ᶠ[𝓝 (x₀, t₀)]
      (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) := by
    refine Filter.mem_of_superset hmem (fun q hq => ?_)
    show (4 * Real.pi)⁻¹ • (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        crossL (ω a q.2) (kf (q.1 - a))) = Work.LWP.biotSavart (fun y => ω y q.2) q.1
    have hR : R + ‖q.1‖ ≤ ρ := by
      have h1 : ‖q.1‖ ≤ ‖x₀‖ + 1 := by
        have h2 := norm_add_le (q.1 - x₀) x₀
        rw [sub_add_cancel] at h2
        linarith [h2, hq.1]
      linarith
    rw [biotSavart_ball_integral hM (hbdd q.2 hq.2) (hsupp q.2 hq.2) (hmeas q.2 hq.2) hR]
    simp only [bsField]
  -- ## Step 2.  The integral over the fixed ball `B(0,ρ)` is continuous at `(x₀,t₀)`.
  have hG : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
        ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
      (x₀, t₀) := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    -- the radius of the fixed split
    set Δ : ℝ := min 1 (ε / (4 * (12 * Real.pi * M + 1))) with hΔdef
    have hden : 0 < 12 * Real.pi * M + 1 := by nlinarith [Real.pi_pos, hM]
    have hΔpos : 0 < Δ := by
      rw [hΔdef]
      exact lt_min one_pos (div_pos hε (by nlinarith [Real.pi_pos, hM]))
    have hΔsmall : 6 * Real.pi * M * Δ < ε / 8 := by
      have hden4 : 0 < 4 * (12 * Real.pi * M + 1) := by nlinarith [Real.pi_pos, hM]
      have hle : Δ ≤ ε / (4 * (12 * Real.pi * M + 1)) := by
        rw [hΔdef]; exact min_le_right _ _
      have h6 : 0 ≤ 6 * Real.pi * M := by nlinarith [Real.pi_pos, hM]
      have hstep : 6 * Real.pi * M * Δ
          ≤ 6 * Real.pi * M * (ε / (4 * (12 * Real.pi * M + 1))) :=
        mul_le_mul_of_nonneg_left hle h6
      have hcoef : 6 * Real.pi * M / (4 * (12 * Real.pi * M + 1)) < 1 / 8 := by
        rw [div_lt_iff₀ hden4]
        nlinarith [Real.pi_pos, hM]
      calc 6 * Real.pi * M * Δ
          ≤ 6 * Real.pi * M * (ε / (4 * (12 * Real.pi * M + 1))) := hstep
        _ = ε * (6 * Real.pi * M / (4 * (12 * Real.pi * M + 1))) := by ring
        _ < ε * (1 / 8) := mul_lt_mul_of_pos_left hcoef hε
        _ = ε / 8 := by ring
    -- the outer piece is continuous
    have hO : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
        ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
          crossL (ω a q.2) (kf (q.1 - a))) (x₀, t₀) :=
      continuousAt_integral_crossL_kf_diff hδ hM hΔpos hbdd hmeas htcont
    obtain ⟨r, hrpos, hr⟩ := Metric.continuousAt_iff.mp hO (ε / 2) (by linarith)
    refine ⟨min r (min (Δ / 2) δ), lt_min hrpos (lt_min (by linarith) hδ), fun q hq => ?_⟩
    have hqr : dist q (x₀, t₀) < r := lt_of_lt_of_le hq (min_le_left _ _)
    have hqΔ : ‖q.1 - x₀‖ ≤ Δ / 2 := by
      have h2 : dist q (x₀, t₀) < Δ / 2 :=
        lt_of_lt_of_le hq (le_trans (min_le_right _ _) (min_le_left _ _))
      rw [Prod.dist_eq] at h2
      have h3 : dist q.1 x₀ < Δ / 2 := lt_of_le_of_lt (le_max_left _ _) h2
      rw [dist_eq_norm] at h3
      exact le_of_lt h3
    have hqt : |q.2 - t₀| < δ := by
      have h2 : dist q (x₀, t₀) < δ :=
        lt_of_lt_of_le hq (le_trans (min_le_right _ _) (min_le_right _ _))
      rw [Prod.dist_eq, Real.dist_eq] at h2
      exact lt_of_le_of_lt (le_max_right _ _) h2
    -- the two splitting identities and the inner bound
    have hsplitq : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              crossL (ω a q.2) (kf (q.1 - a)))
          + (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              crossL (ω a q.2) (kf (q.1 - a))) :=
      integral_crossL_kf_split (ω := ω) hM (hbdd q.2 hqt) (hmeas q.2 hqt) hΔpos hqΔ
    have hsplit0 : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a t₀) (kf (x₀ - a)))
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              crossL (ω a t₀) (kf (x₀ - a)))
          + (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              crossL (ω a t₀) (kf (x₀ - a))) :=
      integral_crossL_kf_split (ω := ω) (x := x₀) hM (hbdd t₀ (by simpa using hδ))
        (hmeas t₀ (by simpa using hδ)) hΔpos (by rw [sub_self, norm_zero]; linarith)
    rw [hsplitq, hsplit0]
    set A : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ), crossL (ω a q.2) (kf (q.1 - a)) with hA
    set B : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ), crossL (ω a q.2) (kf (q.1 - a)) with hB
    set C : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ), crossL (ω a t₀) (kf (x₀ - a)) with hC
    set D : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ), crossL (ω a t₀) (kf (x₀ - a)) with hD
    have hAb : ‖A‖ ≤ 6 * Real.pi * M * Δ := by
      rw [hA]
      refine le_trans ?_ (le_of_eq (by ring : M * (4 * Real.pi * (3 * Δ / 2)) = 6 * Real.pi * M * Δ))
      exact norm_setIntegral_crossL_kf_inter_le (ω := ω) hM (hbdd q.2 hqt) hΔpos hqΔ
    have hCb : ‖C‖ ≤ 6 * Real.pi * M * Δ := by
      rw [hC]
      refine le_trans ?_ (le_of_eq (by ring : M * (4 * Real.pi * (3 * Δ / 2)) = 6 * Real.pi * M * Δ))
      exact norm_setIntegral_crossL_kf_inter_le (ω := ω) (x := x₀) hM
        (hbdd t₀ (by simpa using hδ)) hΔpos (by rw [sub_self, norm_zero]; linarith)
    have hBd : ‖B - D‖ < ε / 2 := by
      rw [← dist_eq_norm, hB, hD]
      exact hr hqr
    have hfin : dist (A + B) (C + D) < ε := by
      rw [dist_eq_norm]
      have heq : (A + B) - (C + D) = (A - C) + (B - D) := by abel
      rw [heq]
      have h1 := norm_add_le (A - C) (B - D)
      have h2 := norm_sub_le A C
      linarith
    exact hfin
  -- ## Step 3.  Put the pieces together.
  have hΦ : ContinuousAt (fun q : Work.LWP.R3 × ℝ => (4 * Real.pi)⁻¹ •
        ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
      (x₀, t₀) := hG.const_smul ((4 * Real.pi)⁻¹)
  exact hΦ.congr hrepr

end Work.CoreResiduals.BiotSavart
