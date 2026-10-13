import Mathlib

open scoped Topology

namespace Work.WilE2

/-- If `φ` has nonzero derivative `c` at `u`, then `φ` is injective on a punctured
neighbourhood of `u`.  Indeed `h.tendsto_slope` says the slope `slope φ u` tends to `c`
along `𝓝[{u}ᶜ] u`; since `c ≠ 0`, the slope is eventually nonzero, and a slope can only
vanish at `t ≠ u` if `φ t = φ u`. -/
theorem exists_dist_ne_of_hasDerivAt_ne_zero {φ : ℝ → ℝ} {u c : ℝ}
    (h : HasDerivAt φ c u) (hc : c ≠ 0) :
    ∃ ε > 0, ∀ t, dist t u < ε → t ≠ u → φ t ≠ φ u := by
  have h2 : ∀ᶠ z in 𝓝[{u}ᶜ] u, slope φ u z ≠ 0 := h.tendsto_slope.eventually_ne hc
  rw [eventually_nhdsWithin_iff] at h2
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ε, hε, h3⟩ := h2
  refine ⟨ε, hε, fun t ht htu hcon => ?_⟩
  have hs : slope φ u t = 0 := by
    rw [slope_def_field, hcon, sub_self, zero_div]
  exact h3 ht (by simpa using htu) hs

end Work.WilE2
