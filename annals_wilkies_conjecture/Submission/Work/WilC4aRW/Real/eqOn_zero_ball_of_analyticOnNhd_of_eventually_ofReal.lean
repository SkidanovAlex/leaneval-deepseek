import Mathlib
import Submission.Work.WilC4aRW.Real.frequently_of_eventually_ofReal

namespace Work.WilC4aRW.Real

/-- If a subset `S` of `ℂ` contains all real points `s` in a neighbourhood of `0`, then (as `ℂ` is a
normed space and the reals accumulate at `0` from every direction) the point `0` lies in the closure
of `S \ {0}`. -/
theorem zero_mem_closure_sdiff_singleton_of_eventually_ofReal {S : Set ℂ}
    (h : ∀ᶠ s : ℝ in nhds 0, (s : ℂ) ∈ S) : (0 : ℂ) ∈ closure (S \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hR : {s : ℝ | (s : ℂ) ∈ S} ∈ nhds (0 : ℝ) := Filter.eventually_iff.mp h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hR
  -- pick a *nonzero* real point `s` that is `ε`-close to `0` and lies in `S`
  set s : ℝ := min δ ε / 2 with hsdef
  have hs_pos : 0 < s := by rw [hsdef]; linarith [lt_min hδpos hε]
  have hs_lt_δ : s < δ := by rw [hsdef]; linarith [min_le_left δ ε]
  have hs_lt_ε : s < ε := by rw [hsdef]; linarith [min_le_right δ ε]
  have hsS : (s : ℂ) ∈ S := hδ (by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs_pos]
    exact hs_lt_δ)
  refine ⟨(s : ℂ), ⟨hsS, ?_⟩, ?_⟩
  · exact fun h0 => hs_pos.ne' (Complex.ofReal_eq_zero.mp h0)
  · have hdist : dist (0 : ℂ) (s : ℂ) = |s| := by simp
    rw [hdist, abs_of_pos hs_pos]
    exact hs_lt_ε

/-- A function which is analytic on a ball around `0` in `ℂ` and which vanishes at the real points
arbitrarily close to `0` vanishes on the whole ball: the real points accumulate at `0`, so the
identity principle for analytic functions applies. -/
theorem eqOn_zero_ball_of_analyticOnNhd_of_eventually_ofReal {ρ : ℝ} (hρ : 0 < ρ) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 ρ))
    (hreal : ∀ᶠ s : ℝ in nhds 0, g (s:ℂ) = 0) :
    Set.EqOn g 0 (Metric.ball 0 ρ) := by
  refine hg.eqOn_zero_of_preconnected_of_mem_closure (convex_ball (0 : ℂ) ρ).isPreconnected
    (Metric.mem_ball_self hρ) (zero_mem_closure_sdiff_singleton_of_eventually_ofReal ?_)
  filter_upwards [hreal] with s hs using hs

end Work.WilC4aRW.Real
