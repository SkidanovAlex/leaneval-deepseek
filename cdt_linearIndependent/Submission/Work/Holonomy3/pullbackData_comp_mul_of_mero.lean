import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# Scaling of pullback data (`PullbackData f (z ↦ φ (r z)) (1/r) …`)

If the pullback of `f` along `φ` is meromorphic on the unit disc with polynomial denominator `P`
(`Submission.CDTPlan.PullbackMero f φ`, i.e. `f(φ z) = N z / P.eval z` as a germ at `0`, with `N`
holomorphic on `ball 0 1` and `P.eval 0 ≠ 0`), then the pullback along the rescaled map
`z ↦ φ (r z)` (`r > 0`) is meromorphic with the same *polynomial* denominator rescaled,
`P.comp (C r * X)`, and numerator `z ↦ N (r z)`.

The point of the widening of the holomorphy radius: for `‖z‖ < 1/r` one has `‖r z‖ < 1`, so
`z ↦ N (r z)` is analytic on `ball 0 (1/r)`; this is exactly the function `N` of
`Work.Holonomy3.PullbackData f (z ↦ φ (r z)) (1/r)`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open Filter Topology
open scoped BigOperators

/-- The scaling `z ↦ r z` (`r > 0`) maps the ball of radius `1/r` into the unit ball. -/
private lemma mapsTo_scale_ball (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (fun z : ℂ => (r : ℂ) * z) (Metric.ball 0 (1 / r)) (Metric.ball 0 1) := by
  intro z hz
  have hzn : ‖z‖ < 1 / r := by simpa [Metric.mem_ball, dist_zero_right] using hz
  simp only [Metric.mem_ball, dist_zero_right]
  have hnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  rw [norm_mul, hnorm]
  calc r * ‖z‖ < r * (1 / r) := mul_lt_mul_of_pos_left hzn hr
    _ = 1 := by field_simp

/-- The scaling `z ↦ r z` tends to `0` at `0`. -/
private lemma tendsto_scale_ball (r : ℝ) : Tendsto (fun z : ℂ => (r : ℂ) * z) (𝓝 0) (𝓝 0) := by
  simpa using (tendsto_const_nhds.mul tendsto_id :
    Tendsto (fun z : ℂ => (r : ℂ) * z) (𝓝 0) (𝓝 ((r : ℂ) * 0)))

/-- **Scaling of meromorphic pullbacks.**  A meromorphic pullback with polynomial denominator
rescales to a meromorphic pullback: the denominator becomes `P.comp (C r * X)` (still nonvanishing
at `0`) and the numerator `z ↦ N (r z)`, which is analytic on the ball of radius `1/r`. -/
theorem pullbackData_comp_mul_of_mero {f : PowerSeries ℚ} {φ : ℂ → ℂ}
    (h : Submission.CDTPlan.PullbackMero f φ) {r : ℝ} (hr : 0 < r) :
    ∃ (N : ℂ → ℂ) (P : Polynomial ℂ), PullbackData f (fun z => φ (r * z)) (1/r) N P := by
  obtain ⟨P, N, hP0, hN, hgerm⟩ := h
  refine ⟨fun z => N (r * z), P.comp (Polynomial.C (r : ℂ) * Polynomial.X), ?_, ?_, ?_⟩
  · -- the rescaled polynomial denominator still does not vanish at `0`
    rw [Polynomial.eval_comp]
    simp [hP0]
  · -- the rescaled numerator is analytic on `ball 0 (1/r)`
    have hN' : AnalyticOnNhd ℂ N (Metric.ball 0 1) := hN.analyticOnNhd Metric.isOpen_ball
    have hlin : AnalyticOnNhd ℂ (fun z : ℂ => (r : ℂ) * z) (Metric.ball 0 (1 / r)) := by
      have hd : DifferentiableOn ℂ (fun z : ℂ => (r : ℂ) * z) (Metric.ball 0 (1 / r)) :=
        (differentiableOn_const (r : ℂ)).mul differentiableOn_id
      exact hd.analyticOnNhd Metric.isOpen_ball
    have hcomp := hN'.comp hlin (mapsTo_scale_ball r hr)
    simpa [Function.comp_def] using hcomp
  · -- the `HasSum` germ at `0` transports along the continuous scaling `z ↦ r z`
    have h2 := Filter.Tendsto.eventually
      (p := fun w : ℂ => HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * φ w ^ n)
        (N w / P.eval w)) (tendsto_scale_ball r) hgerm
    simpa [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using h2

end Work.Holonomy3
