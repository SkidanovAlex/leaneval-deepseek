import Mathlib
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harnack_inequality
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

/-!
# Harnack's inequality on a chart ball

The Euclidean Harnack inequality for non-negative harmonic functions on a closed ball
(`Commons.Analysis.Complex.Harmonic.harnack_inequality`) is transported to a *chart ball* of a
Riemann surface: a non-negative harmonic function on `chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ`
is, at points at chart distance `≤ ρ/2` from the centre, comparable to its value at the centre, with
the absolute constant `5`.
-/

open Filter Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.SimplyConnected.ABS

/-- Translation invariance of harmonicity (the direction needed for Harnack): if `F` is harmonic on
the closed ball of centre `a` and radius `R`, then `ζ ↦ F (ζ + a)` is harmonic on the closed ball of
centre `0` and radius `R`.  (Composition with the analytic shift `ζ ↦ ζ + a`.) -/
theorem harmonicOnNhd_comp_add {F : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F (Metric.closedBall a R)) :
    InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => F (ζ + a)) (Metric.closedBall (0 : ℂ) R) := by
  intro ζ hζ
  have hζ' : ζ + a ∈ Metric.closedBall a R := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ ⊢
    have h : ζ + a - a = ζ := by ring
    rw [h]
    simpa using hζ
  exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
    (f := fun z : ℂ => z + a) (x := ζ) (analyticAt_id.add analyticAt_const) (hF (ζ + a) hζ')

/-- **Harnack's inequality on a chart ball** (Riemann-surface form).

Let `h ≥ 0` be harmonic on the chart ball of centre `p` and radius `ρ` (with the closed Euclidean
ball of radius `ρ` inside the chart target, so that the chart ball is an honest disc).  Then for
every `x` in the ball at chart distance `≤ ρ/2` from the centre, `h x ≤ 5 * h p` and
`h p ≤ 5 * h x`. -/
theorem harnack_inequality_chartBall {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {p : X} {ρ : ℝ} (hρ : 0 < ρ)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target)
    {h : X → ℝ}
    (hh : Submission.HarmonicOnX h (Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ))
    (hpos : ∀ x ∈ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ, 0 ≤ h x)
    {x : X} (hx : x ∈ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
    (hx2 : ‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ ≤ ρ / 2) :
    h x ≤ 5 * h p ∧ h p ≤ 5 * h x := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc
  set a : ℂ := c p with ha
  set w : ℂ := c x with hw
  set F : ℂ → ℝ := h ∘ c.symm with hF
  have hpsrc : p ∈ c.source := mem_chart_source ℂ p
  have haeq : c.symm a = p := by rw [ha]; exact c.left_inv hpsrc
  have hxsrc : x ∈ c.source := (Submission.mem_chartBall.mp hx).1
  have hxeq : c.symm w = x := by rw [hw]; exact c.left_inv hxsrc
  have hwball : w ∈ Metric.ball a ρ := by
    rw [hw, ha]; exact (Submission.mem_chartBall.mp hx).2
  have hwt : ‖w - a‖ < ρ := by
    have h := Metric.mem_ball.mp hwball
    rwa [dist_eq_norm] at h
  have hwt2 : ‖w - a‖ ≤ ρ / 2 := by rw [hw, ha]; exact hx2
  set R : ℝ := (ρ + ‖w - a‖) / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith [norm_nonneg (w - a)]
  have hRlt : R < ρ := by rw [hR]; linarith
  have hwtR : ‖w - a‖ < R := by rw [hR]; linarith
  -- `F` is harmonic on the closed Euclidean ball of centre `a` and radius `R`
  have hFharm : InnerProductSpace.HarmonicOnNhd F (Metric.closedBall a R) := by
    intro z hz
    have hzball : z ∈ Metric.ball a ρ := by
      rw [Metric.mem_ball]
      have h1 : dist z a ≤ R := Metric.mem_closedBall.mp hz
      linarith [hRlt]
    have hztgt : z ∈ c.target := htgt (Metric.ball_subset_closedBall hzball)
    have hysrc : c.symm z ∈ c.source := c.map_target hztgt
    have hyball : c.symm z ∈ Submission.chartBall c a ρ :=
      Submission.mem_chartBall.mpr ⟨hysrc, by rw [c.right_inv hztgt]; exact hzball⟩
    have hAt : Submission.HarmonicOnXAt h (c.symm z) := hh (c.symm z) hyball
    have hiff := (Submission.HarmonicOnXAt_iff_chart (u := h) (x := c.symm z) (y := p)
      (by rw [← hc]; exact hysrc)).mp hAt
    rw [← hc, c.right_inv hztgt] at hiff
    simpa [hF] using hiff
  -- positivity of the shifted function on the closed Euclidean ball of radius `R`
  have hpos' : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ (fun ζ : ℂ => F (ζ + a)) z := by
    intro z hz
    have hzball : z + a ∈ Metric.ball a ρ := by
      rw [Metric.mem_ball]
      have hdist : dist (z + a) a = ‖z‖ := by
        rw [dist_eq_norm]
        congr 1
        ring
      rw [hdist]
      linarith [hz, hRlt]
    have hztgt : z + a ∈ c.target := htgt (Metric.ball_subset_closedBall hzball)
    have hysrc : c.symm (z + a) ∈ c.source := c.map_target hztgt
    have hyball : c.symm (z + a) ∈ Submission.chartBall c a ρ :=
      Submission.mem_chartBall.mpr ⟨hysrc, by rw [c.right_inv hztgt]; exact hzball⟩
    have h := hpos _ hyball
    simpa [hF] using h
  have hshift : InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => F (ζ + a))
      (Metric.closedBall (0 : ℂ) R) := harmonicOnNhd_comp_add hFharm
  have hH := Commons.Analysis.Complex.Harmonic.harnack_inequality hshift hpos' (w := w - a) hwtR
  obtain ⟨hlo, hhi⟩ := hH
  have hhi' : F w ≤ ((R + ‖w - a‖) / (R - ‖w - a‖)) * F a := by
    simpa [show w - a + a = w from by ring, zero_add] using hhi
  have hlo' : ((R - ‖w - a‖) / (R + ‖w - a‖)) * F a ≤ F w := by
    simpa [show w - a + a = w from by ring, zero_add] using hlo
  have hdenpos : 0 < R - ‖w - a‖ := by linarith [hwtR]
  have hnumpos : 0 < R + ‖w - a‖ := by linarith [hRpos, norm_nonneg (w - a)]
  have hRt_hi : R + ‖w - a‖ ≤ 5 * (R - ‖w - a‖) := by linarith [hR, hwt2]
  have hratio_hi : (R + ‖w - a‖) / (R - ‖w - a‖) ≤ 5 := by
    rw [div_le_iff₀ hdenpos]
    exact hRt_hi
  have hratio_lo : (R - ‖w - a‖) / (R + ‖w - a‖) ≤ 5 := by
    rw [div_le_iff₀ hnumpos]
    linarith [hR, hwt2, norm_nonneg (w - a)]
  have hFa : F a = h p := by rw [hF, Function.comp_apply, haeq]
  have hFw : F w = h x := by rw [hF, Function.comp_apply, hxeq]
  have hxnn : 0 ≤ h x := hpos x hx
  have hpnn : 0 ≤ h p := by
    refine hpos p ?_
    rw [Submission.mem_chartBall]
    exact ⟨hpsrc, by rw [← ha]; exact Metric.mem_ball_self hρ⟩
  constructor
  · rw [← hFw, ← hFa]
    calc F w ≤ ((R + ‖w - a‖) / (R - ‖w - a‖)) * F a := hhi'
      _ ≤ 5 * F a := mul_le_mul_of_nonneg_right hratio_hi (by rw [hFa]; exact hpnn)
  · rw [← hFa, ← hFw]
    have hq : 0 < (R - ‖w - a‖) / (R + ‖w - a‖) := div_pos hdenpos hnumpos
    have h1 : F a ≤ F w / ((R - ‖w - a‖) / (R + ‖w - a‖)) := by
      rw [le_div_iff₀ hq]
      calc F a * ((R - ‖w - a‖) / (R + ‖w - a‖))
          = ((R - ‖w - a‖) / (R + ‖w - a‖)) * F a := by ring
        _ ≤ F w := hlo'
    have h2 : F w / ((R - ‖w - a‖) / (R + ‖w - a‖))
        = F w * ((R + ‖w - a‖) / (R - ‖w - a‖)) := by
      rw [div_div_eq_mul_div, mul_div_assoc]
    rw [h2] at h1
    calc F a ≤ F w * ((R + ‖w - a‖) / (R - ‖w - a‖)) := h1
      _ ≤ F w * 5 := mul_le_mul_of_nonneg_left hratio_hi (by rw [hFw]; exact hxnn)
      _ = 5 * F w := by ring

/-- **The local Harnack neighbourhood.**  Let `h ≥ 0` be harmonic on an open set `U`, and let `y ∈ U`
admit a chart ball `B` of radius `ρ` around `y` with the closed Euclidean ball inside the chart
target and `B ⊆ U`.  Then every point of the *shrunk* chart ball of radius `ρ / 2` is comparable to
`y`:

  `h q ≤ 5 * h y`  and  `h y ≤ 5 * h q`.

This is the form in which the chart-ball Harnack inequality is used to build Harnack chains: it
says that every point of `U` has a neighbourhood on which all non-negative harmonic functions are
comparable, uniformly in the function. -/
theorem harnack_comparable_on_shrunk_ball {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} {h : X → ℝ} (hh : Submission.HarmonicOnX h U)
    (hpos : ∀ x ∈ U, 0 ≤ h x) {y : X} {ρ : ℝ} (hρ : 0 < ρ)
    (htgt : Metric.closedBall ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hsub : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ U) :
    ∀ q ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) (ρ / 2),
      h q ≤ 5 * h y ∧ h y ≤ 5 * h q := by
  intro q hq
  have hρ2 : 0 < ρ / 2 := by linarith
  have hmono : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) (ρ / 2) ⊆
      Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ :=
    fun z hz => ⟨hz.1, Metric.ball_subset_ball (by linarith) hz.2⟩
  have hqρ : q ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ := hmono hq
  have hdist : ‖(chartAt ℂ y) q - (chartAt ℂ y) y‖ ≤ ρ / 2 := by
    have h := Metric.mem_ball.mp hq.2
    rw [dist_eq_norm] at h
    exact h.le
  exact harnack_inequality_chartBall (p := y) (ρ := ρ) (hρ := hρ) (htgt := htgt)
    (h := h) (hh := hh.mono hsub) (hpos := fun z hz => hpos z (hsub hz))
    (x := q) (hx := hqρ) (hx2 := hdist)

end Work.SimplyConnected.ABS
