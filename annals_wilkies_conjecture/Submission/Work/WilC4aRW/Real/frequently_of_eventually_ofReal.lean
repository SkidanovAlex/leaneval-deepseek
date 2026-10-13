import Mathlib

namespace Work.WilC4aRW.Real

/-- If a property of complex numbers holds eventually along the real line near `0`,
then it holds frequently in any punctured neighbourhood of `0` in `ℂ`.

Indeed, `h` gives a real `ε > 0` with `P (s : ℂ)` for `|s| < ε`, while a punctured
neighbourhood of `0 : ℂ` contains a punctured disc of some radius `δ > 0`; any positive
real `t < min ε δ` then witnesses both conditions. -/
theorem frequently_of_eventually_ofReal {P : ℂ → Prop}
    (h : ∀ᶠ s : ℝ in nhds 0, P (s : ℂ)) : ∃ᶠ z in nhdsWithin (0:ℂ) {0}ᶜ, P z := by
  rw [Filter.frequently_iff]
  intro T hT
  rw [Metric.mem_nhdsWithin_iff] at hT
  obtain ⟨δ, hδpos, hδT⟩ := hT
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at h
  obtain ⟨ε, hεpos, hεP⟩ := h
  set t : ℝ := min δ ε / 2 with ht
  have hmin : 0 < min δ ε := lt_min hδpos hεpos
  have htpos : 0 < t := by rw [ht]; linarith
  have htδ : t < δ := by rw [ht]; have := min_le_left δ ε; linarith
  have htε : t < ε := by rw [ht]; have := min_le_right δ ε; linarith
  refine ⟨(t : ℂ), hδT ⟨?_, ?_⟩, hεP ?_⟩
  · rw [Metric.mem_ball, ← Complex.ofReal_zero, Complex.isometry_ofReal.dist_eq, Real.dist_eq,
      sub_zero, abs_of_pos htpos]
    exact htδ
  · rw [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    exact ne_of_gt htpos
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htε

end Work.WilC4aRW.Real
