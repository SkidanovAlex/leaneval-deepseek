import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Geom

/-- If `x ∈ A` and `y ∉ A` then the segment from `x` to `y` meets the frontier of `A`,
at a point `z` that is no farther from `x` nor from `y` than `dist y x`.

The point `z` is the first point of the segment `[x, y]` lying in `A`, i.e. the
intersection of the segment with `A` is `{x + t • (y - x) : 0 ≤ t ≤ sSup T}` where
`T = {t ∈ [0,1] | x + t • (y - x) ∈ A}`.  Both distance bounds then follow from the
convexity of the closed balls around `x` and `y` of radius `dist y x`. -/
theorem exists_mem_frontier_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} {x y : E} (hx : x ∈ A) (hy : y ∉ A) :
    ∃ z ∈ frontier A, dist z x ≤ dist y x ∧ dist z y ≤ dist y x := by
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  have hd : 0 < dist y x := dist_pos.mpr hxy.symm
  let f : ℝ → E := fun t => x + t • (y - x)
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => x := continuous_const
    have h2 : Continuous fun t : ℝ => t • (y - x) := continuous_id.smul continuous_const
    exact h1.add h2
  let T : Set ℝ := {t | 0 ≤ t ∧ t ≤ 1 ∧ f t ∈ A}
  have h0T : (0 : ℝ) ∈ T := ⟨le_refl 0, zero_le_one, by simp [f, hx]⟩
  have hTne : T.Nonempty := ⟨0, h0T⟩
  have hTbd : BddAbove T := ⟨1, fun t ht => ht.2.1⟩
  set s : ℝ := sSup T with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef]; exact le_csSup hTbd h0T
  have hs1 : s ≤ 1 := by
    rw [hsdef]; exact csSup_le hTne (fun t ht => ht.2.1)
  have hsup : ∀ t ∈ T, t ≤ s := by
    intro t ht; rw [hsdef]; exact le_csSup hTbd ht
  refine ⟨f s, ?_, ?_, ?_⟩
  · rw [frontier_eq_closure_inter_closure]
    constructor
    · -- `f s` is a limit of points of `A`, approached from the left
      have hscl : s ∈ closure T := by
        rw [hsdef]; exact csSup_mem_closure hTne hTbd
      have himg : f s ∈ closure (f '' T) :=
        image_closure_subset_closure_image (s := T) hfc ⟨s, hscl, rfl⟩
      exact closure_mono (fun z hz => by rcases hz with ⟨t, ht, rfl⟩; exact ht.2.2) himg
    · rcases lt_or_eq_of_le hs1 with hlt | heq
      · -- `f s` is also a limit of points outside `A`, approached from the right
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨δ, hδpos, hδf⟩ := (Metric.continuousAt_iff.mp hfc.continuousAt) ε hε
        set m : ℝ := min δ ((1 - s) / 2) with hmdef
        have hmpos : 0 < m := by
          rw [hmdef]; exact lt_min hδpos (by linarith)
        have hmle : m ≤ (1 - s) / 2 := by rw [hmdef]; exact min_le_right _ _
        set t : ℝ := s + m / 2 with htdef
        have ht_gt : s < t := by rw [htdef]; linarith
        have ht_le : t ≤ 1 := by rw [htdef]; linarith
        have ht_notA : f t ∉ A := by
          intro hmem
          have htT : t ∈ T := ⟨by rw [htdef]; linarith, ht_le, hmem⟩
          have hle := hsup t htT
          rw [htdef] at hle
          linarith
        have hdist : dist (f t) (f s) < ε := by
          apply hδf
          rw [Real.dist_eq, abs_of_nonneg (by rw [htdef]; linarith : (0:ℝ) ≤ t - s)]
          have hmle' : m ≤ δ := by rw [hmdef]; exact min_le_left _ _
          rw [htdef]
          linarith
        exact ⟨f t, ht_notA, by rw [dist_comm]; exact hdist⟩
      · -- the endpoint `y` is already outside `A`
        have hfs : f s = y := by
          rw [heq]; simp [f]
        rw [hfs]
        exact subset_closure hy
  · -- `f s` lies in the segment `[x, y]`, hence in the closed ball around `x`
    have hzseg : f s ∈ segment ℝ x y := by
      rw [segment_eq_image']
      exact ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have h1 : f s ∈ Metric.closedBall x (dist y x) :=
      Convex.segment_subset (convex_closedBall x (dist y x))
        (by rw [Metric.mem_closedBall, dist_self]; exact hd.le)
        (by rw [Metric.mem_closedBall])
        hzseg
    simpa [Metric.mem_closedBall] using h1
  · -- and in the closed ball around `y`
    have hzseg : f s ∈ segment ℝ x y := by
      rw [segment_eq_image']
      exact ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have h1 : f s ∈ Metric.closedBall y (dist y x) :=
      Convex.segment_subset (convex_closedBall y (dist y x))
        (by rw [Metric.mem_closedBall, dist_comm])
        (by rw [Metric.mem_closedBall, dist_self]; exact hd.le)
        hzseg
    simpa [Metric.mem_closedBall] using h1

end NK.NUV2.Geom
