import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.kf_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity of the parametrised Biot–Savart integral over a fixed set avoiding a ball.**

For a spacetime vorticity `ω` obeying the uniform bound `‖ω a t‖ ≤ M` on the window
`|t - t₀| < δ`, with ae-strongly-measurable slices there and continuous in `t` at `t₀` for every
fixed `a`, the map

`(x,t) ↦ ∫ a in B(0,ρ) \ B(x₀,Δ), crossL (ω a t) (kf (x - a))`

is continuous at `(x₀,t₀)`, for any `ρ` and any `Δ > 0`.

This is the "outer piece" of the peel-off argument: the integration set is *fixed* (it does not
depend on `x`), and for `x ∈ B(x₀,Δ/2)` the integrand is bounded on it by the constant
`M * (Δ/2)⁻²`, since `a ∉ B(x₀,Δ)` gives `‖x - a‖ ≥ Δ/2`; so dominated convergence
(`MeasureTheory.continuousAt_of_dominated`) applies, the dominating function being the
`B(0,ρ)`-indicator of that constant. For fixed `a ≠ x₀` the integrand
`(x,t) ↦ crossL (ω a t) (kf (x - a))` is continuous at `(x₀,t₀)` (continuity of `crossL`, of `kf`
away from `0`, and `htcont a`).

Useful identifications: `Work.StabilityFar.Decay.bsK_eq_crossL` rewrites
`crossL (ω a t) (kf (x - a))` as `Work.LWP.BiotSavart.bsK (fun y => ω y t) x a`, and
`Work.LWP.BiotSavart.norm_bsK_le` gives the pointwise bound
`‖bsK ω x a‖ ≤ (‖x-a‖^3)⁻¹ * ‖ω a‖ * ‖x-a‖`, while
`Work.LWP.BiotSavart.aestronglyMeasurable_bsK` gives the measurability in `a`. -/
theorem continuousAt_integral_crossL_kf_diff {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ M ρ Δ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hbdd : ∀ t : ℝ, |t - t₀| < δ → ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hmeas : ∀ t : ℝ, |t - t₀| < δ →
      MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
        Work.StabilityFar.Decay.crossL (ω a q.2) (Work.StabilityFar.Decay.kf (q.1 - a)))
      (x₀, t₀) := by
  classical
  set S : Set Work.LWP.R3 := Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball x₀ Δ with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]; exact measurableSet_ball.diff measurableSet_ball
  have hballfin : volume (Metric.closedBall (0 : Work.LWP.R3) ρ) ≠ ⊤ :=
    (isCompact_closedBall (0 : Work.LWP.R3) ρ).measure_lt_top.ne
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hballfin
      (measure_mono (by rw [hSdef]; exact fun a ha => Metric.ball_subset_closedBall ha.1))
  have hbi : Integrable (fun _ : Work.LWP.R3 => M * ((Δ / 2) ^ (2 : ℕ))⁻¹)
      (volume.restrict S) :=
    integrableOn_const hSfin
  have hmain : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      ∫ a, Work.StabilityFar.Decay.crossL (ω a q.2) (Work.StabilityFar.Decay.kf (q.1 - a))
        ∂(volume.restrict S)) (x₀, t₀) := by
    apply MeasureTheory.continuousAt_of_dominated (bound := fun _ : Work.LWP.R3 =>
      M * ((Δ / 2) ^ (2 : ℕ))⁻¹)
    · -- a.e. strong measurability of the integrand in `a`
      filter_upwards [Metric.ball_mem_nhds (x₀, t₀) hδ] with q hq
      have hqt : |q.2 - t₀| < δ := by
        have h1 : dist q.2 t₀ ≤ dist q (x₀, t₀) := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        rw [Real.dist_eq] at h1
        exact lt_of_le_of_lt h1 (Metric.mem_ball.mp hq)
      refine MeasureTheory.AEStronglyMeasurable.mono_measure (ν := volume.restrict S) ?_
        MeasureTheory.Measure.restrict_le_self
      rw [show (fun a => Work.StabilityFar.Decay.crossL (ω a q.2)
            (Work.StabilityFar.Decay.kf (q.1 - a)))
          = (fun a => Work.LWP.BiotSavart.bsK (fun y => ω y q.2) q.1 a) from
        funext (fun a => (Work.StabilityFar.Decay.bsK_eq_crossL (fun y => ω y q.2) q.1 a).symm)]
      exact Work.LWP.BiotSavart.aestronglyMeasurable_bsK (hmeas q.2 hqt) q.1
    · -- the constant dominating function
      have hε : (0 : ℝ) < min (Δ / 2) δ := lt_min (by linarith) hδ
      filter_upwards [Metric.ball_mem_nhds (x₀, t₀) hε] with q hq
      have hdq : dist q (x₀, t₀) < min (Δ / 2) δ := Metric.mem_ball.mp hq
      have hd1 : dist q.1 x₀ < Δ / 2 := by
        have h1 : dist q.1 x₀ ≤ dist q (x₀, t₀) := by
          rw [Prod.dist_eq]; exact le_max_left _ _
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 hdq) (min_le_left _ _)
      have hqt : |q.2 - t₀| < δ := by
        have h1 : dist q.2 t₀ ≤ dist q (x₀, t₀) := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        rw [Real.dist_eq] at h1
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 hdq) (min_le_right _ _)
      refine MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun a ha => ?_)
      rw [hSdef] at ha
      have hax : a ≠ x₀ := by
        intro h
        exact ha.2 (by rw [h]; exact Metric.mem_ball_self hΔ)
      have hna : Δ ≤ ‖a - x₀‖ := by
        have h : Δ ≤ dist a x₀ := by
          simpa only [Metric.mem_ball, not_lt] using ha.2
        simpa only [dist_eq_norm] using h
      have hxq : Δ / 2 < ‖q.1 - a‖ := by
        have h1 : ‖a - x₀‖ ≤ ‖a - q.1‖ + ‖q.1 - x₀‖ := by
          have h := norm_add_le (a - q.1) (q.1 - x₀)
          rwa [sub_add_sub_cancel] at h
        have h2 : ‖q.1 - x₀‖ < Δ / 2 := by simpa only [dist_eq_norm] using hd1
        have h3 : ‖a - q.1‖ = ‖q.1 - a‖ := norm_sub_rev _ _
        linarith
      have hpos : 0 < ‖q.1 - a‖ := by linarith
      have hkey : (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖q.1 - a‖ = (‖q.1 - a‖ ^ (2 : ℕ))⁻¹ := by
        have h3 : ‖q.1 - a‖ ^ (3 : ℕ) = ‖q.1 - a‖ ^ (2 : ℕ) * ‖q.1 - a‖ := by ring
        rw [h3, mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
      have hbsK : ‖Work.StabilityFar.Decay.crossL (ω a q.2)
            (Work.StabilityFar.Decay.kf (q.1 - a))‖
          ≤ (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖ := by
        rw [← Work.StabilityFar.Decay.bsK_eq_crossL (fun y => ω y q.2) q.1 a]
        exact Work.LWP.BiotSavart.norm_bsK_le _ _ _
      have hstep1 : (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖
          = ‖ω a q.2‖ * ((‖q.1 - a‖ ^ (2 : ℕ))⁻¹) := by
        rw [show (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖
            = ‖ω a q.2‖ * ((‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖q.1 - a‖) by ring, hkey]
      have hinv : (‖q.1 - a‖ ^ (2 : ℕ))⁻¹ ≤ ((Δ / 2) ^ (2 : ℕ))⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (by positivity) (le_of_lt hxq) 2
      calc ‖Work.StabilityFar.Decay.crossL (ω a q.2) (Work.StabilityFar.Decay.kf (q.1 - a))‖
          ≤ (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖ := hbsK
        _ = ‖ω a q.2‖ * ((‖q.1 - a‖ ^ (2 : ℕ))⁻¹) := hstep1
        _ ≤ M * ((Δ / 2) ^ (2 : ℕ))⁻¹ :=
            mul_le_mul (hbdd q.2 hqt a) hinv (by positivity) hM
    · exact hbi
    · -- pointwise continuity of the integrand at `(x₀,t₀)` for `a ∈ S`
      refine MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun a ha => ?_)
      rw [hSdef] at ha
      have hax : a ≠ x₀ := by
        intro h
        exact ha.2 (by rw [h]; exact Metric.mem_ball_self hΔ)
      have hne : x₀ - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hax)
      have h1 : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω a q.2) (x₀, t₀) :=
        (htcont a).comp continuous_snd.continuousAt
      have hsub : ContinuousAt (fun q : Work.LWP.R3 × ℝ => q.1 - a) (x₀, t₀) :=
        ContinuousAt.sub (continuous_fst.continuousAt :
          ContinuousAt (fun q : Work.LWP.R3 × ℝ => q.1) (x₀, t₀))
          (continuousAt_const :
            ContinuousAt (fun _ : Work.LWP.R3 × ℝ => a) (x₀, t₀))
      have h2 : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
          Work.StabilityFar.Decay.kf (q.1 - a)) (x₀, t₀) :=
        ContinuousAt.comp (x := (x₀, t₀)) (g := Work.StabilityFar.Decay.kf)
          (f := fun q : Work.LWP.R3 × ℝ => q.1 - a)
          ((Work.StabilityFar.Decay.kf_hasFDerivAt (x₀ - a) hne).continuousAt) hsub
      have h3 : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
          Work.StabilityFar.Decay.crossL (ω a q.2)) (x₀, t₀) :=
        Work.StabilityFar.Decay.continuous_crossL.continuousAt.comp h1
      exact h3.clm_apply h2
  exact hmain

end Work.CoreResiduals.BiotSavart
