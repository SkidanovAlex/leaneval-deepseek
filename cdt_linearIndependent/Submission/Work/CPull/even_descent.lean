import Mathlib
import Submission.Work.CPull.defs
import Submission.Commons.Analysis.Analytic.even_analytic_factor_sq_onBall

/-!
# Area CPull — even functions descend through the square map on the unit disc

`Work.CPull.even_descent`: an even holomorphic function `E` on the unit disc is a function of
`z ^ 2` — there is a holomorphic `N` on the disc with `N (z ^ 2) = E z` for every `z` in the
disc.

The work is almost entirely already in the workspace library:

* `Commons.Analysis.Analytic.even_analytic_factor_sq_onBall` descends a power series which is
  even on a ball of (extended) radius `R` to a function with a power series on the ball of
  radius `R ^ 2`;
* the only missing input for the statement at hand is that a function holomorphic on the *open*
  unit disc admits a power series of radius exactly `1` at the origin
  (`hasFPowerSeriesOnBall_one` below).  Mathlib's `DifferentiableOn.hasFPowerSeriesOnBall`
  only produces series on strictly smaller closed discs; the radius is upgraded to `1` by
  transferring it along `HasFPowerSeriesOnBall.exchange_radius`
  (uniqueness of the power series of a function at a point), and then assembling the structure
  by hand, the `hasSum` field being a limiting statement over radii `< 1`.
-/

namespace Work.CPull

open scoped Topology ENNReal NNReal

/-- A function holomorphic on the open unit disc has a power series with radius `1` at the
origin.  (Standard: the radius of convergence of the Taylor expansion at `0` is at least the
distance from `0` to the nearest singularity.) -/
theorem hasFPowerSeriesOnBall_one (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E (Metric.ball 0 1)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall E p 0 1 := by
  -- a power series on the closed disc of radius `1/2`
  have hcd : DifferentiableOn ℂ E (Metric.closedBall (0 : ℂ) (1/2 : ℝ≥0)) := by
    refine hE.mono ?_
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    have h : ((1/2 : ℝ≥0) : ℝ) = 1/2 := by norm_num
    rw [h] at hz
    linarith
  obtain ⟨p, hp⟩ : ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesOnBall E p 0 ((1/2 : ℝ≥0) : ℝ≥0∞) :=
    ⟨_, hcd.hasFPowerSeriesOnBall (by norm_num)⟩
  -- the same series is valid at every radius `< 1`
  have hfam : ∀ r' : ℝ≥0, 0 < r' → (r' : ℝ≥0∞) < 1 →
      HasFPowerSeriesOnBall E p 0 (r' : ℝ≥0∞) := by
    intro r' hr'pos hr'lt
    have hcd' : DifferentiableOn ℂ E (Metric.closedBall (0 : ℂ) r') := by
      refine hE.mono ?_
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hz
      simp only [Metric.mem_ball, dist_zero_right]
      have h1 : (r' : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_one]; exact hr'lt
      have h2 : (r' : ℝ) < 1 := by
        have := ENNReal.coe_lt_coe.mp h1
        exact_mod_cast this
      linarith
    exact hp.exchange_radius (hcd'.hasFPowerSeriesOnBall hr'pos)
  refine ⟨p, ?_, by norm_num, ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt ?_
    intro s hs
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0]; exact zero_le
    · exact (hfam s (pos_iff_ne_zero.mpr h0) hs).r_le
  · intro y hy
    have hy1 : ‖y‖ₑ < (1 : ℝ≥0∞) := by rwa [mem_eball_zero_iff] at hy
    obtain ⟨r', hyr', hr'1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hy1
    have hr'1' : r' < 1 := by
      have h : (r' : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_one]; exact hr'1
      exact ENNReal.coe_lt_coe.mp h
    set rs : ℝ≥0 := max r' (1/2) with hrs
    have hrs_pos : 0 < rs := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hrs_le1 : rs < 1 := by rw [hrs]; exact max_lt hr'1' (by norm_num)
    have hrs_lt : (rs : ℝ≥0∞) < 1 := by
      have h := ENNReal.coe_lt_coe.mpr hrs_le1
      rwa [ENNReal.coe_one] at h
    have hyrs : y ∈ Metric.eball (0 : ℂ) (rs : ℝ≥0∞) := by
      rw [mem_eball_zero_iff]
      exact lt_of_lt_of_le hyr' (ENNReal.coe_le_coe.mpr (le_max_left _ _))
    exact (hfam rs hrs_pos hrs_lt).hasSum hyrs

/-- The unit `eball` and `ball` of `ℂ` agree. -/
private lemma eball_one_eq_ball_one :
    Metric.eball (0 : ℂ) (1 : ℝ≥0∞) = Metric.ball (0 : ℂ) 1 := by
  rw [← ENNReal.coe_one, Metric.eball_coe]
  norm_num

/-- **Even descent.**  An even holomorphic function on the unit disc is a holomorphic function
of `z ^ 2`. -/
theorem even_descent (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E (Metric.ball 0 1))
    (heven : ∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, N (z ^ 2) = E z := by
  obtain ⟨p, hp⟩ := hasFPowerSeriesOnBall_one E hE
  have heven' : ∀ z : ℂ, z ∈ Metric.eball (0 : ℂ) (1 : ℝ≥0∞) → E (-z) = E z := by
    intro z hz
    exact heven z (by rwa [eball_one_eq_ball_one] at hz)
  obtain ⟨g, q, hgq, -, hgeq⟩ :=
    Commons.Analysis.Analytic.even_analytic_factor_sq_onBall (f := E) (p := p) (R := 1)
      hp heven'
  simp only [one_pow] at hgq hgeq
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.eball (0 : ℂ) (1 : ℝ≥0∞) := by rwa [eball_one_eq_ball_one]
    exact ((hgq.analyticAt_of_mem hz').differentiableAt).differentiableWithinAt
  · intro z hz
    exact hgeq z (by rwa [eball_one_eq_ball_one])

end Work.CPull
