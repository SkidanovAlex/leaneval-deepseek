import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germCHelpers

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section

/-- **Local Lipschitz bound at `0` with an explicit constant.**  An analytic function vanishing at
`0` satisfies `‖f u‖ ≤ (‖f'(0)‖ + ε) ‖u‖` on a small ball around `0`.  Factor `f u = u · dslope f 0 u`
via `mul_dslope_eq` and bound the (analytic, hence continuous) `dslope` near the origin. -/
lemma analytic_lipschitz_add {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → ‖f u‖ ≤ (‖deriv f 0‖ + ε) * ‖u‖ := by
  have hcont : ContinuousAt (dslope f 0) 0 := (analyticAt_dslope hf).continuousAt
  have hd0 : dslope f 0 0 = deriv f 0 := dslope_same f 0
  have hb : ∀ᶠ u in 𝓝 (0 : ℂ), ‖dslope f 0 u‖ ≤ ‖deriv f 0‖ + ε := by
    have hmem : ∀ᶠ u in 𝓝 (0 : ℂ), dslope f 0 u ∈ Metric.ball (deriv f 0) ε := by
      have h := hcont.eventually_mem (Metric.ball_mem_nhds (dslope f 0 0) hε)
      rwa [hd0] at h
    filter_upwards [hmem] with u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have h2 : ‖dslope f 0 u‖ ≤ ‖dslope f 0 u - deriv f 0‖ + ‖deriv f 0‖ := by
      linarith [norm_sub_norm_le (dslope f 0 u) (deriv f 0)]
    linarith
  obtain ⟨δ, hδ0, hδ⟩ := exists_ball_of_eventually hb
  refine ⟨δ, hδ0, fun u hu => ?_⟩
  have hu' : u ∈ Metric.ball (0 : ℂ) δ := by
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hb' := hδ u hu'
  rw [← mul_dslope_eq (f := f) h0, norm_mul]
  calc ‖u‖ * ‖dslope f 0 u‖ ≤ ‖u‖ * (‖deriv f 0‖ + ε) :=
        mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
    _ = (‖deriv f 0‖ + ε) * ‖u‖ := by ring

/-- **Small-ball facts about the stable germ curve.**

There is a radius `ρY > 0` such that on the closed ball of radius `ρY` the second coordinate
`w ↦ (germC a h w).2` maps strictly into the ball of radius `ρY` (so the ball is invariant for the
linearising parameter), the germ step `germC w ↦ germC (λ w)` is a regular pair throughout the
ball, and the second coordinate is injective on the ball.

Route: the second coordinate has derivative `(1 - a) / 2` at `0` of modulus `< 1/2`, so for small
`w` it satisfies `‖(germC a h w).2‖ ≤ (1/2 + ε) ‖w‖ < ρY`; `Work.EQ.germC_facts` supplies the
regularity of the germ step and the injectivity of the second coordinate on a suitable ball, and the
smallest of the three radii works. -/
theorem germC_small_ball_maps {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ ρY : ℝ, 0 < ρY ∧
      (∀ w : ℂ, ‖w‖ ≤ ρY → ‖(Work.EQ.germC a h w).2‖ < ρY) ∧
      (∀ v : ℂ, ‖v‖ < ρY → Work.EQ.RegPair a (Work.EQ.germC a h v)
        (Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) * v))) ∧
      Set.InjOn (fun w : ℂ => (Work.EQ.germC a h w).2) (Metric.ball (0 : ℂ) ρY) := by
  obtain ⟨ρ, hρpos, hAnC, hgerm0, hregC, hinjY, hderivY⟩ := germC_facts ha0 ha1 hh
  -- analyticity of the second coordinate at `0`
  have hYan : AnalyticAt ℂ (fun u : ℂ => (germC a h u).2) 0 := by
    have hmemC : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρpos
    have hproj : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (germC a h 0) :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
    have h1 := hproj.comp (hAnC 0 hmemC)
    simpa [Function.comp_def] using h1
  have hY0 : (fun u : ℂ => (germC a h u).2) 0 = 0 := by
    show (germC a h 0).2 = 0
    rw [hgerm0]
  -- the derivative of the second coordinate is `(1 - a)/2`, of modulus `< 3/4`
  have hc_lt : ‖deriv (fun u : ℂ => (germC a h u).2) 0‖ < (3 / 4 : ℝ) := by
    rw [hderivY]
    have hc0 : (0 : ℝ) ≤ (1 - a) / 2 := by linarith
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hc0]
    linarith
  obtain ⟨δ, hδpos, hδ⟩ :=
    analytic_lipschitz_add hYan hY0 (ε := 3 / 4 - ‖deriv (fun u : ℂ => (germC a h u).2) 0‖)
      (by linarith)
  have hconst : ‖deriv (fun u : ℂ => (germC a h u).2) 0‖
      + (3 / 4 - ‖deriv (fun u : ℂ => (germC a h u).2) 0‖) = 3 / 4 := by ring
  -- the working radius
  set ρY : ℝ := min δ ρ / 2 with hρYdef
  have hmin : 0 < min δ ρ := lt_min hδpos hρpos
  have hρYpos : 0 < ρY := by rw [hρYdef]; linarith
  have hρYlt : ρY < min δ ρ := by rw [hρYdef]; linarith
  have hρYltδ : ρY < δ := lt_of_lt_of_le hρYlt (min_le_left _ _)
  have hρYleρ : ρY ≤ ρ := le_of_lt (lt_of_lt_of_le hρYlt (min_le_right _ _))
  refine ⟨ρY, hρYpos, ?_, ?_, ?_⟩
  · intro w hw
    have hwδ : ‖w‖ < δ := lt_of_le_of_lt hw hρYltδ
    have hb : ‖(germC a h w).2‖ ≤ (3 / 4) * ‖w‖ := by
      have h := hδ w hwδ
      rwa [hconst] at h
    calc ‖(germC a h w).2‖ ≤ (3 / 4) * ‖w‖ := hb
      _ ≤ (3 / 4) * ρY := mul_le_mul_of_nonneg_left hw (by norm_num)
      _ < ρY := by linarith
  · intro v hv
    have hvρ : v ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le hv hρYleρ
    exact (hregC v hvρ).1
  · exact hinjY.mono (Metric.ball_subset_ball hρYleρ)

end

end Work.EQ
