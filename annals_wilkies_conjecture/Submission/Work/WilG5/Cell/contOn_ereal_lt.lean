import Mathlib

namespace Work.WilG5.Cell

/-- If `a` is continuous on `C` and `a y0 < c` (with `c` a genuine real, coerced into `EReal`),
then `a` stays strictly below `c` on a full coordinate ball around `y0` intersected with `C`.

This is the "openness of `Set.Iio ↑c`" fact: `Set.Iio (c : EReal)` is open in `EReal`, so its
preimage is a relative neighbourhood of `y0` in `C`, and a metric ball sits inside it. -/
theorem contOn_ereal_lt {n : ℕ} {a : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (ha : ContinuousOn a C) {y0 : Fin n → ℝ} (hy0 : y0 ∈ C) {c : ℝ} (h : a y0 < (c : EReal)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ C, (∀ i, |y' i - y0 i| < δ) → a y' < (c : EReal) := by
  -- `Set.Iio ↑c` is open in `EReal`.
  have hU : IsOpen (Set.Iio (c : EReal)) := isOpen_Iio
  -- hence its preimage is a relative neighbourhood of `y0` in `C`.
  have hmem : a ⁻¹' Set.Iio (c : EReal) ∈ nhdsWithin y0 C :=
    (ha y0 hy0).tendsto (hU.mem_nhds h)
  obtain ⟨u, hu, hut⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hmem
  -- a metric ball around `y0` is contained in `u`.
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1 hu
  refine ⟨δ, hδpos, ?_⟩
  intro y' hy'C hy'
  -- the coordinatewise bound gives a bound on the sup-distance.
  have hdist : dist y' y0 < δ := by
    rw [dist_pi_lt_iff hδpos]
    intro i
    rw [Real.dist_eq]
    exact hy' i
  have hyu : y' ∈ u := hδ (Metric.mem_ball.2 hdist)
  have := hut ⟨hyu, hy'C⟩
  simpa using this

end Work.WilG5.Cell
