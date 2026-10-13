import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsIntegrand_param
import Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity of the outer part of the parametrised Biot–Savart derivative integral.**

For a spacetime vorticity that is `c`-Hölder in `x` with a constant `C ≥ 0` uniform on the time
window `|t - t₀| < δ`, jointly continuous at `(x₀,t₀)` and continuous in `t` at `t₀` for every
fixed `x`, the map `(x,t) ↦ ∫_{B(0,ρ) \ B(x₀,Δ)} bsIntegrand (ω(·,t)) x a da` is continuous at
`(x₀,t₀)`, for `0 < Δ ≤ 2`.

Proof route: use `MeasureTheory.continuousAt_of_dominated` with the *constant* (integrable)
dominating function `bound a = B(0,ρ).indicator (fun a => K * (1 + ‖a‖^{c-3})) a`, where
`exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖+1) (δ := Δ/2)` supplies `K`; the pointwise
bound on `B(0,ρ) \ B(x₀,Δ)` is `bsIntegrand_indicator_le` (from `continuous_bsDerivCLM`), whose
hypotheses `‖x - x₀‖ ≤ Δ/2`, `|t - t₀| < δ` hold eventually near `(x₀,t₀)`; measurability is
`aestronglyMeasurable_bsIntegrand` composed with `continuous_of_holder`; and for fixed
`a ∈ B(0,ρ) \ B(x₀,Δ)` (so `a ≠ x₀`) continuity in `(x,t)` is
`continuousAt_bsIntegrand_param` (imported). -/
theorem continuousAt_bsIntegrand_outer {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ c C ρ Δ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ t : ℝ, |t - t₀| < δ →
      ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ C * ‖a - b‖ ^ c)
    (hjoint : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀))
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀)
    (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
        Work.CoreResiduals.BiotSavart.bsIntegrand (fun y => ω y q.2) q.1 a) (x₀, t₀) := by
  -- The dominating constant `K` for the outer region, from `exists_rpow_dom_bound`.
  obtain ⟨K, hK0, hK⟩ := exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖ + 1) (δ := Δ / 2)
    hc hC (by positivity) (by linarith)
  have hmeas : MeasurableSet ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  -- The dominating function is integrable: an indicator of a ball times `1 + ‖·‖^{c-3}`.
  have hbdint : Integrable ((Metric.ball (0 : Work.LWP.R3) ρ).indicator
      (fun a : Work.LWP.R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((integrableOn_one_add_norm_rpow_ball (c - 3) ρ (by linarith)).const_mul K)
  -- Near `(x₀,t₀)` both remaining hypotheses of the pointwise bound hold.
  have hnhds : Metric.ball x₀ (Δ / 2) ×ˢ Metric.ball t₀ δ ∈ 𝓝 (x₀, t₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.ball_mem_nhds x₀ (by linarith)) (Metric.ball_mem_nhds t₀ hδ)
  -- The truncated integrand and the dominating function, as local definitions (unification on
  -- the large integrand would otherwise be slow).
  let F : (Work.LWP.R3 × ℝ) → Work.LWP.R3 → (Work.LWP.R3 →L[ℝ] Work.LWP.R3) := fun q a =>
    ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)).indicator
      (bsIntegrand (fun y => ω y q.2) q.1) a
  let bd : Work.LWP.R3 → ℝ := (Metric.ball (0 : Work.LWP.R3) ρ).indicator
      (fun a : Work.LWP.R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))
  have hmain : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ∫ a, F q a) (x₀, t₀) := by
    refine MeasureTheory.continuousAt_of_dominated (F := F) (bound := bd) ?_ ?_ ?_ ?_
    · -- Measurability in `a`, for `q` near `(x₀,t₀)` (where `ω(·,q.2)` is Hölder, hence continuous).
      filter_upwards [hnhds] with q hq
      have hω : Continuous (fun y : Work.LWP.R3 => ω y q.2) :=
        continuous_of_holder hc hC (hhold q.2 (by
          have := hq.2
          rw [Metric.mem_ball, Real.dist_eq] at this
          exact this))
      exact (aestronglyMeasurable_bsIntegrand hω q.1).indicator hmeas
    · -- The pointwise domination, for `q` near `(x₀,t₀)`.
      filter_upwards [hnhds] with q hq
      filter_upwards with a
      have hx : ‖q.1 - x₀‖ ≤ Δ / 2 := by
        have := hq.1
        rw [Metric.mem_ball, dist_eq_norm] at this
        exact le_of_lt this
      have ht : |q.2 - t₀| < δ := by
        have := hq.2
        rwa [Metric.mem_ball, Real.dist_eq] at this
      exact bsIntegrand_indicator_le (K := K) (ρ := ρ) (Δ := Δ) (x₀ := x₀) hC
        (hhold q.2 ht) hK hK0 hΔ2 hx a
    · exact hbdint
    · -- For a fixed `a` the integrand is continuous in `q`: either `a` is in the outer region
      -- (then `a ≠ x₀` and the parametrised continuity applies), or the indicator vanishes.
      refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : a ∈ (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)
      · have hax : a ≠ x₀ := by
          intro h; rw [h] at ha; exact ha.2 (Metric.mem_ball_self hΔ)
        have hc' : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
            bsIntegrand (fun y => ω y q.2) q.1 a) (x₀, t₀) :=
          continuousAt_bsIntegrand_param hjoint htcont hax
        exact hc'.congr (Filter.Eventually.of_forall fun q =>
          (Set.indicator_of_mem ha (bsIntegrand (fun y => ω y q.2) q.1)).symm)
      · refine ContinuousAt.congr
          (continuousAt_const (y := (0 : Work.LWP.R3 →L[ℝ] Work.LWP.R3)))
          (Filter.Eventually.of_forall fun q => ?_)
        show (0 : Work.LWP.R3 →L[ℝ] Work.LWP.R3) = ((Metric.ball (0 : Work.LWP.R3) ρ) \
          (Metric.ball x₀ Δ)).indicator (bsIntegrand (fun y => ω y q.2) q.1) a
        rw [Set.indicator_of_notMem ha]
  -- Rewrite the restricted integral as the integral of the truncated integrand over the whole space.
  exact hmain.congr (Filter.Eventually.of_forall fun q => by
    show (∫ a, ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)).indicator
          (bsIntegrand (fun y => ω y q.2) q.1) a)
        = ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
            bsIntegrand (fun y => ω y q.2) q.1 a
    rw [MeasureTheory.integral_indicator hmeas])

end Work.CoreResiduals.BiotSavart
