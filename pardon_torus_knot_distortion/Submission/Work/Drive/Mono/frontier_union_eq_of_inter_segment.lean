import Mathlib

/-!
# The frontier of the union of two convex sets meeting in a segment

If `A`, `B ⊆ ℂ` are compact convex with non-empty interior, if `A ∩ B` is the non-degenerate
segment `[m₁,m₂]`, and if `A`, `B` lie in opposite closed half-spaces of a non-zero linear
functional `f` (`A ⊆ {f ≤ c}`, `B ⊆ {f ≥ c}`), then

`frontier (A ∪ B) = (frontier A \ [m₁,m₂]°) ∪ (frontier B \ [m₁,m₂]°)`,

where `[m₁,m₂]° = segment ℝ m₁ m₂ \ {m₁, m₂}` is the open segment.

The proof goes through the interior identity
`interior (A ∪ B) = interior A ∪ interior B ∪ [m₁,m₂]°`:
* the open segment is contained in `interior (A ∪ B)` (a neighbourhood of a relative interior
  point `z` of the segment is covered by the two triangles spanned by `z` and an interior point
  of `A`, resp. of `B`, on either side of the common supporting line);
* a point of `interior (A ∪ B)` which lies in `A` is either interior to `A` or on the segment;
* the endpoints `m₁`, `m₂` are not interior to `A ∪ B` (a limiting argument using that the
  points of a small ball on either side of the level `f = c` lie in `A`, resp. `B`).
-/
set_option maxHeartbeats 2000000

namespace Work.Drive.Mono

open Set Metric Filter
open scoped Convex Pointwise Topology

noncomputable section

private lemma eq_re_smul_one_add_im_smul_I (w : ℂ) :
    w = w.re • (1 : ℂ) + w.im • (Complex.I : ℂ) := by
  apply Complex.ext
  · simp
  · simp

private lemma apply_re_im (f : ℂ →L[ℝ] ℝ) (w : ℂ) :
    f w = w.re * f 1 + w.im * f (Complex.I) := by
  conv_lhs => rw [eq_re_smul_one_add_im_smul_I w]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

private lemma exists_smul_of_apply_eq_zero {f : ℂ →L[ℝ] ℝ} (hf : f ≠ 0) {u z : ℂ}
    (hu : u ≠ 0) (hfu : f u = 0) (hz : f z = 0) : ∃ t : ℝ, z = t • u := by
  have h1 : u.re * f 1 + u.im * f (Complex.I) = 0 := by rw [← apply_re_im f u, hfu]
  have h2 : z.re * f 1 + z.im * f (Complex.I) = 0 := by rw [← apply_re_im f z, hz]
  rcases eq_or_ne (f 1) 0 with hf1 | hf1
  · have hfI : f (Complex.I) ≠ 0 := by
      intro h0
      apply hf
      ext w
      rw [apply_re_im f w, hf1, h0]
      simp
    have huim : u.im = 0 := by
      rw [hf1, mul_zero, zero_add] at h1
      exact Or.resolve_right (mul_eq_zero.mp h1) hfI
    have hzim : z.im = 0 := by
      rw [hf1, mul_zero, zero_add] at h2
      exact Or.resolve_right (mul_eq_zero.mp h2) hfI
    have hu' : u = u.re • (1 : ℂ) := by
      conv_lhs => rw [eq_re_smul_one_add_im_smul_I u]
      rw [huim, zero_smul, add_zero]
    have hz' : z = z.re • (1 : ℂ) := by
      conv_lhs => rw [eq_re_smul_one_add_im_smul_I z]
      rw [hzim, zero_smul, add_zero]
    have hure : u.re ≠ 0 := by
      intro h0
      apply hu
      rw [hu', h0, zero_smul]
    refine ⟨z.re / u.re, ?_⟩
    calc z = z.re • (1 : ℂ) := hz'
      _ = ((z.re / u.re) * u.re) • (1 : ℂ) := by rw [div_mul_cancel₀ _ hure]
      _ = (z.re / u.re) • (u.re • (1 : ℂ)) := by rw [smul_smul]
      _ = (z.re / u.re) • u := by
            congr 1
            exact hu'.symm
  · set c₀ : ℂ := (-(f (Complex.I) / f 1)) • (1 : ℂ) + Complex.I with hc₀
    have hure : u.re = -(u.im * f (Complex.I)) / f 1 := by
      rw [eq_div_iff hf1]; linarith
    have hzre : z.re = -(z.im * f (Complex.I)) / f 1 := by
      rw [eq_div_iff hf1]; linarith
    have hu' : u = u.im • c₀ := by
      conv_lhs => rw [eq_re_smul_one_add_im_smul_I u]
      rw [hure, hc₀, smul_add, smul_smul,
        show -(u.im * f (Complex.I)) / f 1 = u.im * (-(f (Complex.I) / f 1)) by
          field_simp]
    have hz' : z = z.im • c₀ := by
      conv_lhs => rw [eq_re_smul_one_add_im_smul_I z]
      rw [hzre, hc₀, smul_add, smul_smul,
        show -(z.im * f (Complex.I)) / f 1 = z.im * (-(f (Complex.I) / f 1)) by
          field_simp]
    have huim : u.im ≠ 0 := by
      intro h0
      apply hu
      rw [hu', h0, zero_smul]
    refine ⟨z.im / u.im, ?_⟩
    calc z = z.im • c₀ := hz'
      _ = ((z.im / u.im) * u.im) • c₀ := by rw [div_mul_cancel₀ _ huim]
      _ = (z.im / u.im) • (u.im • c₀) := by rw [smul_smul]
      _ = (z.im / u.im) • u := by
            congr 1
            exact hu'.symm

/-- A point maximising a non-zero linear functional on a convex set is not an interior point. -/
private lemma not_mem_interior_of_le {A : Set ℂ} {f : ℂ →L[ℝ] ℝ} {c : ℝ} (hf : f ≠ 0)
    (hA : A ⊆ {x | f x ≤ c}) {x : ℂ} (hxc : f x = c) : x ∉ interior A := by
  intro hxint
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, Metric.ball x ε ⊆ A := by
    rw [mem_interior_iff_mem_nhds] at hxint
    exact Metric.mem_nhds_iff.mp hxint
  obtain ⟨v, hv⟩ : ∃ v : ℂ, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext v; exact h v)
  set w : ℂ := if 0 < f v then v else -v with hw
  have hwpos : 0 < f w := by
    by_cases h : 0 < f v
    · simp only [hw, if_pos h]; exact h
    · have hvlt : f v < 0 := lt_of_le_of_ne (le_of_not_gt h) hv
      simp only [hw, if_neg h, map_neg]
      linarith
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by
    rw [ht]; positivity
  have htw : ‖t • w‖ < ε := by
    rw [norm_smul, Real.norm_of_nonneg htpos.le, ht, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖w‖ + 1))]
    nlinarith [norm_nonneg w]
  have hmem : x + t • w ∈ A := by
    apply hsub
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : x + t • w - x = t • w := by abel
    rw [h1]; exact htw
  have hle : f (x + t • w) ≤ c := hA hmem
  rw [map_add, map_smul, hxc, smul_eq_mul] at hle
  nlinarith [hwpos, htpos]

/-- Membership in a level set of a non-zero functional, in the direction of a point `a` with
smaller value. -/
private lemma exists_pos_apply (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0) : ∃ v : ℂ, 0 < f v := by
  obtain ⟨v, hv⟩ : ∃ v : ℂ, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext v; exact h v)
  rcases lt_or_gt_of_ne hv with h | h
  · exact ⟨-v, by rw [map_neg]; linarith⟩
  · exact ⟨v, h⟩

/-! ## The endpoints of the common segment are not interior points of the union -/

private lemma not_mem_interior_union_endpoint {A B : Set ℂ} {f : ℂ →L[ℝ] ℝ} {c : ℝ}
    {x y : ℂ} (hAcl : IsClosed A) (hBcl : IsClosed B) (hf : f ≠ 0)
    (hA : A ⊆ {z | f z ≤ c}) (hB : B ⊆ {z | f z ≥ c})
    (hinter : A ∩ B = segment ℝ x y) (hxy : x ≠ y) :
    x ∉ interior (A ∪ B) := by
  intro hint
  obtain ⟨δ, hδpos, hball⟩ : ∃ δ > 0, ball x δ ⊆ A ∪ B := by
    rw [mem_interior_iff_mem_nhds] at hint
    exact Metric.mem_nhds_iff.mp hint
  have hxc : f x = c := by
    have h : x ∈ A ∩ B := by rw [hinter]; exact left_mem_segment ℝ x y
    exact le_antisymm (hA h.1) (hB h.2)
  have hyc : f y = c := by
    have h : y ∈ A ∩ B := by rw [hinter]; exact right_mem_segment ℝ x y
    exact le_antisymm (hA h.1) (hB h.2)
  have hmemA : ∀ v : ℂ, ‖v‖ < δ → f v < 0 → x + v ∈ A := by
    intro v hv hfv
    have h1 : x + v ∈ A ∪ B := by
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hv
    rcases h1 with h | h
    · exact h
    · have h2 : c ≤ f (x + v) := hB h
      rw [map_add f x v, hxc] at h2
      linarith
  have hmemB : ∀ v : ℂ, ‖v‖ < δ → 0 < f v → x + v ∈ B := by
    intro v hv hfv
    have h1 : x + v ∈ A ∪ B := by
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hv
    rcases h1 with h | h
    · have h2 : f (x + v) ≤ c := hA h
      rw [map_add f x v, hxc] at h2
      linarith
    · exact h
  obtain ⟨w, hw⟩ : ∃ w : ℂ, f w = 1 := by
    obtain ⟨v, hv⟩ : ∃ v : ℂ, f v ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (by ext z; exact h z)
    exact ⟨(f v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  set u : ℂ := y - x with hu
  have hu_ne : u ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hfu : f u = 0 := by rw [hu, map_sub, hyc, hxc, sub_self]
  obtain ⟨α, hαpos, hαδ⟩ : ∃ α : ℝ, 0 < α ∧ α * ‖u‖ < δ := by
    refine ⟨δ / (2 * (‖u‖ + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖u‖ + 1))]
    nlinarith [norm_nonneg u, hδpos]
  have hptA : x - α • u ∈ A := by
    have htend : Tendsto (fun t : ℝ => x + (-(α • u) - t • w)) (𝓝[>] (0:ℝ)) (𝓝 (x + -(α • u))) := by
      have h1 : Tendsto (fun t : ℝ => x + (-(α • u) - t • w)) (𝓝 (0:ℝ))
          (𝓝 (x + -(α • u))) := by
        have h2 := (show Continuous fun t : ℝ => x + (-(α • u) - t • w) by continuity).tendsto 0
        simpa using h2
      exact h1.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), x + (-(α • u) - t • w) ∈ A := by
      have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖-(α • u) - t • w‖ < δ := by
        have hcont : Tendsto (fun t : ℝ => ‖-(α • u) - t • w‖) (𝓝[>] (0:ℝ))
            (𝓝 (‖-(α • u)‖)) := by
          have h1 : Tendsto (fun t : ℝ => ‖-(α • u) - t • w‖) (𝓝 (0:ℝ))
              (𝓝 (‖-(α • u)‖)) := by
            have h2 := (show Continuous fun t : ℝ => ‖-(α • u) - t • w‖ by continuity).tendsto 0
            simpa using h2
          exact h1.mono_left nhdsWithin_le_nhds
        have hlt : ‖-(α • u)‖ < δ := by
          rw [norm_neg, norm_smul, Real.norm_of_nonneg hαpos.le]
          exact hαδ
        exact hcont.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds hlt)
      filter_upwards [self_mem_nhdsWithin, h2] with t htpos htlt
      have htpos' : 0 < t := htpos
      apply hmemA
      · exact htlt
      · rw [map_sub, map_neg, map_smul, map_smul, hfu, smul_zero, neg_zero, zero_sub, hw,
          smul_eq_mul, mul_one]
        linarith
    have := hAcl.mem_of_tendsto htend hev
    simpa [sub_eq_add_neg] using this
  have hptB : x - α • u ∈ B := by
    have htend : Tendsto (fun t : ℝ => x + (-(α • u) + t • w)) (𝓝[>] (0:ℝ)) (𝓝 (x + -(α • u))) := by
      have h1 : Tendsto (fun t : ℝ => x + (-(α • u) + t • w)) (𝓝 (0:ℝ))
          (𝓝 (x + -(α • u))) := by
        have h2 := (show Continuous fun t : ℝ => x + (-(α • u) + t • w) by continuity).tendsto 0
        simpa using h2
      exact h1.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), x + (-(α • u) + t • w) ∈ B := by
      have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖-(α • u) + t • w‖ < δ := by
        have hcont : Tendsto (fun t : ℝ => ‖-(α • u) + t • w‖) (𝓝[>] (0:ℝ))
            (𝓝 (‖-(α • u)‖)) := by
          have h1 : Tendsto (fun t : ℝ => ‖-(α • u) + t • w‖) (𝓝 (0:ℝ))
              (𝓝 (‖-(α • u)‖)) := by
            have h2 := (show Continuous fun t : ℝ => ‖-(α • u) + t • w‖ by continuity).tendsto 0
            simpa using h2
          exact h1.mono_left nhdsWithin_le_nhds
        have hlt : ‖-(α • u)‖ < δ := by
          rw [norm_neg, norm_smul, Real.norm_of_nonneg hαpos.le]
          exact hαδ
        exact hcont.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds hlt)
      filter_upwards [self_mem_nhdsWithin, h2] with t htpos htlt
      have htpos' : 0 < t := htpos
      apply hmemB
      · exact htlt
      · rw [map_add, map_neg, map_smul, map_smul, hfu, smul_zero, neg_zero, zero_add, hw,
          smul_eq_mul, mul_one]
        linarith
    have := hBcl.mem_of_tendsto htend hev
    simpa [sub_eq_add_neg] using this
  have hboth : x - α • u ∈ A ∩ B := ⟨hptA, hptB⟩
  rw [hinter, segment_eq_image'] at hboth
  obtain ⟨t, ht, ht'⟩ := hboth
  simp only [] at ht'
  have hsub : -(α • u) = t • u := by
    have h' : t • (y - x) = -(α • u) := by
      exact add_left_cancel (a := x) (by simpa [sub_eq_add_neg] using ht')
    conv_rhs => rw [hu]
    exact h'.symm
  have hzero : ((-α) - t) • u = 0 := by
    rw [sub_smul, neg_smul, hsub, sub_self]
  have ht0 : -α - t = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hu_ne
  linarith [ht.1]


/-! ## Points of the relative interior of the common segment are interior points of the union -/

private lemma exists_neg_apply (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0) : ∃ v : ℂ, f v < 0 := by
  obtain ⟨v, hv⟩ := exists_pos_apply f hf
  exact ⟨-v, by rw [map_neg]; linarith⟩

private lemma relint_subset_interior_union {A B : Set ℂ} {f : ℂ →L[ℝ] ℝ} {c : ℝ}
    {x y : ℂ} (hAc : Convex ℝ A) (hBc : Convex ℝ B)
    (hAne : (interior A).Nonempty) (hBne : (interior B).Nonempty)
    (hf : f ≠ 0) (hA : A ⊆ {z | f z ≤ c}) (hB : B ⊆ {z | f z ≥ c})
    (hinter : A ∩ B = segment ℝ x y) (hxy : x ≠ y) :
    segment ℝ x y \ {x, y} ⊆ interior (A ∪ B) := by
  have hxc : f x = c := by
    have h : x ∈ A ∩ B := by rw [hinter]; exact left_mem_segment ℝ x y
    exact le_antisymm (hA h.1) (hB h.2)
  have hyc : f y = c := by
    have h : y ∈ A ∩ B := by rw [hinter]; exact right_mem_segment ℝ x y
    exact le_antisymm (hA h.1) (hB h.2)
  set u : ℂ := y - x with hu
  have hu_ne : u ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hfu : f u = 0 := by rw [hu, map_sub, hyc, hxc, sub_self]
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ interior A, f a < c := by
    obtain ⟨a, ha⟩ := hAne
    refine ⟨a, ha, ?_⟩
    rcases lt_or_eq_of_le (show f a ≤ c from hA (interior_subset ha)) with h | h
    · exact h
    · exfalso
      obtain ⟨v, hv⟩ := exists_pos_apply f hf
      obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ball a ε ⊆ A := by
        rw [mem_interior_iff_mem_nhds] at ha
        exact Metric.mem_nhds_iff.mp ha
      set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have htv : ‖t • v‖ < ε := by
        rw [norm_smul, Real.norm_of_nonneg htpos.le, ht, div_mul_eq_mul_div,
          div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖v‖ + 1))]
        nlinarith [norm_nonneg v]
      have hmem : a + t • v ∈ A := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : a + t • v - a = t • v := by abel
        rw [h1]; exact htv
      have h2 : f (a + t • v) ≤ c := hA hmem
      rw [map_add, map_smul, h, smul_eq_mul] at h2
      nlinarith [hv, htpos]
  obtain ⟨b, hb, hfb⟩ : ∃ b ∈ interior B, c < f b := by
    obtain ⟨b, hb⟩ := hBne
    rcases lt_or_eq_of_le (show c ≤ f b from hB (interior_subset hb)) with h | h
    · exact ⟨b, hb, h⟩
    · exfalso
      obtain ⟨v, hv⟩ := exists_neg_apply f hf
      obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ball b ε ⊆ B := by
        rw [mem_interior_iff_mem_nhds] at hb
        exact Metric.mem_nhds_iff.mp hb
      set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have htv : ‖t • v‖ < ε := by
        rw [norm_smul, Real.norm_of_nonneg htpos.le, ht, div_mul_eq_mul_div,
          div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖v‖ + 1))]
        nlinarith [norm_nonneg v]
      have hmem : b + t • v ∈ B := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : b + t • v - b = t • v := by abel
        rw [h1]; exact htv
      have h2 : c ≤ f (b + t • v) := hB hmem
      rw [map_add, map_smul, h.symm, smul_eq_mul] at h2
      nlinarith [hv, htpos]
  intro z hz
  obtain ⟨hzS, hznot⟩ := hz
  have hzx : z ≠ x := fun h => hznot (by rw [h]; exact Set.mem_insert _ _)
  have hzy : z ≠ y := fun h => hznot (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
  obtain ⟨θ, hθ, hzθ⟩ : ∃ θ : ℝ, θ ∈ Set.Icc (0:ℝ) 1 ∧ z = x + θ • u := by
    have hz' : z ∈ segment ℝ x y := hzS
    rw [segment_eq_image'] at hz'
    obtain ⟨θ, hθ, hθ'⟩ := hz'
    simp only [] at hθ'
    exact ⟨θ, hθ, by rw [hu]; exact hθ'.symm⟩
  have hθ0 : 0 < θ := by
    rcases lt_or_eq_of_le hθ.1 with h | h
    · exact h
    · exfalso
      exact hzx (by rw [hzθ, ← h, zero_smul, add_zero])
  have hθ1 : θ < 1 := by
    rcases lt_or_eq_of_le hθ.2 with h | h
    · exact h
    · exfalso
      refine hzy ?_
      rw [hzθ, h, one_smul, hu]
      module
  have hzc : f z = c := by
    have h1 : f (x + θ • u) = f x + θ * f u := by
      rw [map_add, map_smul, smul_eq_mul]
    rw [hzθ, h1, hxc, hfu, mul_zero, add_zero]
  set ρ : ℝ := min θ (1 - θ) * ‖u‖ / 2 with hρdef
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have : 0 < min θ (1 - θ) := lt_min hθ0 (by linarith)
    positivity
  have hlevel : ∀ w : ℂ, f w = c → ‖w - z‖ < ρ → w ∈ segment ℝ x y := by
    intro w hw hwd
    have hfw : f (w - x) = 0 := by rw [map_sub, hw, hxc, sub_self]
    obtain ⟨t, ht⟩ := exists_smul_of_apply_eq_zero hf hu_ne hfu hfw
    have hwu : w = x + t • u := by rw [← ht]; module
    have hdist : ‖(t - θ) • u‖ < min θ (1 - θ) * ‖u‖ / 2 := by
      rw [show (t - θ) • u = w - z by rw [hwu, hzθ]; module]
      rw [← hρdef]; exact hwd
    have hnrm : ‖(t - θ) • u‖ = |t - θ| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
    have ht2 : |t - θ| < min θ (1 - θ) / 2 := by
      have h' : |t - θ| * ‖u‖ < (min θ (1 - θ) / 2) * ‖u‖ := by
        have h2 := hdist
        rw [hnrm] at h2
        have h3 : min θ (1 - θ) * ‖u‖ / 2 = (min θ (1 - θ) / 2) * ‖u‖ := by ring
        rw [h3] at h2
        exact h2
      exact lt_of_mul_lt_mul_right h' (le_of_lt hu_pos)
    have htIcc : t ∈ Icc 0 1 := by
      have h1 : |t - θ| < θ := by
        have := min_le_left θ (1 - θ); linarith
      have h2 : |t - θ| < 1 - θ := by
        have := min_le_right θ (1 - θ); linarith
      exact ⟨by have := (abs_lt.mp h1).1; linarith,
             by have := (abs_lt.mp h2).2; linarith⟩
    rw [segment_eq_image']
    exact ⟨t, htIcc, by rw [← hu]; exact hwu.symm⟩
  have hcapos : 0 < c - f a := by linarith
  have hcbpos : 0 < f b - c := by linarith
  set Ka : ℝ := 1 + ‖f‖ * ‖a - z‖ / (c - f a) with hKa
  set Kb : ℝ := 1 + ‖f‖ * ‖b - z‖ / (f b - c) with hKb
  have hKapos : 0 < Ka := by rw [hKa]; positivity
  have hKbpos : 0 < Kb := by rw [hKb]; positivity
  refine mem_interior_iff_mem_nhds.mpr ?_
  rw [Metric.mem_nhds_iff]
  refine ⟨min (ρ / (4 * Ka)) (min (ρ / (4 * Kb))
      (min ((c - f a) / (2 * (‖f‖ + 1))) ((f b - c) / (2 * (‖f‖ + 1))))),
    lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))), ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hwz1 : ‖w - z‖ < ρ / (4 * Ka) := lt_of_lt_of_le hw (min_le_left _ _)
  have hwz2 : ‖w - z‖ < ρ / (4 * Kb) :=
    lt_of_lt_of_le hw (le_trans (min_le_right _ _) (min_le_left _ _))
  have hwza : ‖w - z‖ < (c - f a) / (2 * (‖f‖ + 1)) :=
    lt_of_lt_of_le hw (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hwzb : ‖w - z‖ < (f b - c) / (2 * (‖f‖ + 1)) :=
    lt_of_lt_of_le hw (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hbnd : |f w - c| ≤ ‖f‖ * ‖w - z‖ := by
    have h1 : f w - c = f (w - z) := by rw [map_sub, hzc]
    rw [h1, ← Real.norm_eq_abs]
    exact f.le_opNorm _
  have hunif : ‖f‖ * ‖w - z‖ < (c - f a) / 2 := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (‖f‖ + 1))] at hwza
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [norm_nonneg f, hwza]
  have hunifb : ‖f‖ * ‖w - z‖ < (f b - c) / 2 := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (‖f‖ + 1))] at hwzb
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [norm_nonneg f, hwzb]
  rcases le_total (f w) c with hle | hle
  · set lam : ℝ := (f w - c) / (f a - c) with hlamdef
    have hlam0 : 0 ≤ lam := by
      rw [hlamdef]
      rw [show (f w - c) / (f a - c) = (c - f w) / (c - f a) by
        rw [show f w - c = -(c - f w) by ring, show f a - c = -(c - f a) by ring,
          neg_div_neg_eq]]
      exact div_nonneg (by linarith) (by linarith)
    have hlamle : lam ≤ 1 / 2 := by
      rw [hlamdef]
      rw [show (f w - c) / (f a - c) = (c - f w) / (c - f a) by
        rw [show f w - c = -(c - f w) by ring, show f a - c = -(c - f a) by ring,
          neg_div_neg_eq]]
      rw [div_le_iff₀ hcapos]
      have h2 := (abs_le.mp hbnd).1
      nlinarith [h2, hunif]
    set z' : ℂ := (1 - lam)⁻¹ • (w - lam • a) with hz'def
    have hz'c : f z' = c := by
      have h1 : f z' = (1 - lam)⁻¹ * (f w - lam * f a) := by
        rw [hz'def, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
      have h2 : lam * (f a - c) = f w - c := by
        rw [hlamdef]
        exact div_mul_cancel₀ _ (by linarith : f a - c ≠ 0)
      have h3 : f w - lam * f a = (1 - lam) * c := by
        have h4 : lam * f a = lam * (f a - c) + lam * c := by ring
        rw [h4, h2]; ring
      rw [h1, h3, ← mul_assoc, inv_mul_cancel₀ (by linarith : (1 : ℝ) - lam ≠ 0), one_mul]
    have hz'dist : ‖z' - z‖ < ρ := by
      have hpos : 0 < (1 - lam)⁻¹ := inv_pos.mpr (by linarith : (0:ℝ) < 1 - lam)
      have heq : z' - z = (1 - lam)⁻¹ • ((w - z) - lam • (a - z)) := by
        rw [hz'def]
        have hc : (1 : ℝ) - lam ≠ 0 := by linarith
        have h2 : (1 - lam)⁻¹ • (w - lam • a) - z
            = (1 - lam)⁻¹ • ((w - lam • a) - (1 - lam) • z) := by
          simp only [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [h2]
        congr 1
        module
      rw [heq, norm_smul, Real.norm_of_nonneg hpos.le]
      have h3 : (1 - lam)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith : (0:ℝ) < 1 - lam) (by norm_num : (0:ℝ) < 2)]
        linarith
      have h4 : ‖(w - z) - lam • (a - z)‖ ≤ ‖w - z‖ + lam * ‖a - z‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg hlam0]
      have h6 : lam ≤ ‖f‖ * ‖w - z‖ / (c - f a) := by
        rw [hlamdef, show (f w - c) / (f a - c) = (c - f w) / (c - f a) by
          rw [show f w - c = -(c - f w) by ring, show f a - c = -(c - f a) by ring,
            neg_div_neg_eq]]
        have h5 : c - f w ≤ ‖f‖ * ‖w - z‖ := by
          have h6 := (abs_le.mp hbnd).1
          linarith
        exact div_le_div_of_nonneg_right h5 hcapos.le
      have h7 : ‖w - z‖ + lam * ‖a - z‖ ≤ ‖w - z‖ * Ka := by
        rw [hKa]
        have e1 : ‖w - z‖ * (1 + ‖f‖ * ‖a - z‖ / (c - f a))
            = ‖w - z‖ + ‖w - z‖ * (‖f‖ * ‖a - z‖ / (c - f a)) := by ring
        have e2 : ‖w - z‖ * (‖f‖ * ‖a - z‖ / (c - f a))
            = (‖f‖ * ‖w - z‖ / (c - f a)) * ‖a - z‖ := by ring
        rw [e1, e2]
        linarith [mul_le_mul_of_nonneg_right h6 (norm_nonneg (a - z))]
      have h10 : ‖w - z‖ * Ka < ρ / 4 := by
        have h4 : 0 < 4 * Ka := by positivity
        have h5 := (lt_div_iff₀ h4).mp hwz1
        nlinarith [h5, hKapos]
      nlinarith [h4, h3, h7, h10, hρpos]
    have hz'S : z' ∈ segment ℝ x y := hlevel z' hz'c hz'dist
    have hdecomp : w = lam • a + (1 - lam) • z' := by
      rw [hz'def]
      rw [show (1 - lam) • ((1 - lam)⁻¹ • (w - lam • a)) = w - lam • a by
        rw [smul_smul, mul_inv_cancel₀ (by linarith : (1 : ℝ) - lam ≠ 0), one_smul]]
      abel
    rw [hdecomp]
    left
    exact hAc (interior_subset ha) ((hinter ▸ hz'S).1) hlam0 (by linarith) (by ring)
  · set mu : ℝ := (f w - c) / (f b - c) with hmudef
    have hmu0 : 0 ≤ mu := by
      rw [hmudef]
      exact div_nonneg (by linarith) (le_of_lt hcbpos)
    have hmule : mu ≤ 1 / 2 := by
      rw [hmudef]
      rw [div_le_iff₀ hcbpos]
      have h2 := (abs_le.mp hbnd).2
      nlinarith [h2, hunifb]
    set z'' : ℂ := (1 - mu)⁻¹ • (w - mu • b) with hz''def
    have hz''c : f z'' = c := by
      have h1 : f z'' = (1 - mu)⁻¹ * (f w - mu * f b) := by
        rw [hz''def, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
      have h2 : mu * (f b - c) = f w - c := by
        rw [hmudef]
        exact div_mul_cancel₀ _ hcbpos.ne'
      have h3 : f w - mu * f b = (1 - mu) * c := by
        have h4 : mu * f b = mu * (f b - c) + mu * c := by ring
        rw [h4, h2]; ring
      rw [h1, h3, ← mul_assoc, inv_mul_cancel₀ (by linarith : (1 : ℝ) - mu ≠ 0), one_mul]
    have hz''dist : ‖z'' - z‖ < ρ := by
      have hpos : 0 < (1 - mu)⁻¹ := inv_pos.mpr (by linarith : (0:ℝ) < 1 - mu)
      have heq : z'' - z = (1 - mu)⁻¹ • ((w - z) - mu • (b - z)) := by
        rw [hz''def]
        have hc : (1 : ℝ) - mu ≠ 0 := by linarith
        have h2 : (1 - mu)⁻¹ • (w - mu • b) - z
            = (1 - mu)⁻¹ • ((w - mu • b) - (1 - mu) • z) := by
          simp only [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [h2]
        congr 1
        module
      rw [heq, norm_smul, Real.norm_of_nonneg hpos.le]
      have h3 : (1 - mu)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith : (0:ℝ) < 1 - mu) (by norm_num : (0:ℝ) < 2)]
        linarith
      have h4 : ‖(w - z) - mu • (b - z)‖ ≤ ‖w - z‖ + mu * ‖b - z‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg hmu0]
      have h6 : mu ≤ ‖f‖ * ‖w - z‖ / (f b - c) := by
        rw [hmudef]
        have h5 : f w - c ≤ ‖f‖ * ‖w - z‖ := by
          exact le_trans (le_abs_self _) hbnd
        exact div_le_div_of_nonneg_right h5 hcbpos.le
      have h7 : ‖w - z‖ + mu * ‖b - z‖ ≤ ‖w - z‖ * Kb := by
        rw [hKb]
        have e1 : ‖w - z‖ * (1 + ‖f‖ * ‖b - z‖ / (f b - c))
            = ‖w - z‖ + ‖w - z‖ * (‖f‖ * ‖b - z‖ / (f b - c)) := by ring
        have e2 : ‖w - z‖ * (‖f‖ * ‖b - z‖ / (f b - c))
            = (‖f‖ * ‖w - z‖ / (f b - c)) * ‖b - z‖ := by ring
        rw [e1, e2]
        linarith [mul_le_mul_of_nonneg_right h6 (norm_nonneg (b - z))]
      have h10 : ‖w - z‖ * Kb < ρ / 4 := by
        have h4 : 0 < 4 * Kb := by positivity
        have h5 := (lt_div_iff₀ h4).mp hwz2
        nlinarith [h5, hKbpos]
      nlinarith [h4, h3, h7, h10, hρpos]
    have hz''S : z'' ∈ segment ℝ x y := hlevel z'' hz''c hz''dist
    have hdecomp : w = mu • b + (1 - mu) • z'' := by
      rw [hz''def]
      rw [show (1 - mu) • ((1 - mu)⁻¹ • (w - mu • b)) = w - mu • b by
        rw [smul_smul, mul_inv_cancel₀ (by linarith : (1 : ℝ) - mu ≠ 0), one_smul]]
      abel
    rw [hdecomp]
    right
    exact hBc (interior_subset hb) ((hinter ▸ hz''S).2) hmu0 (by linarith) (by ring)

/-- **The frontier of a union of two convex sets meeting in a segment.** -/
theorem frontier_union_eq_of_inter_segment {A B : Set ℂ}
    (hAc : Convex ℝ A) (hAcl : IsCompact A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsCompact B) (hBne : (interior B).Nonempty)
    {m₁ m₂ : ℂ} (hm : m₁ ≠ m₂) (hinter : A ∩ B = segment ℝ m₁ m₂)
    (hsep : ∃ (f : ℂ →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ A ⊆ {x | f x ≤ c} ∧ B ⊆ {x | f x ≥ c}) :
    frontier (A ∪ B)
      = (frontier A \ (segment ℝ m₁ m₂ \ {m₁, m₂})) ∪
        (frontier B \ (segment ℝ m₁ m₂ \ {m₁, m₂})) := by
  obtain ⟨f, c, hf, hAf, hBf⟩ := hsep
  have hxAcl : IsClosed A := hAcl.isClosed
  have hxBcl : IsClosed B := hBcl.isClosed
  have hxint : m₁ ∉ interior (A ∪ B) :=
    not_mem_interior_union_endpoint hxAcl hxBcl hf hAf hBf hinter hm
  have hyint : m₂ ∉ interior (A ∪ B) := by
    refine not_mem_interior_union_endpoint hxAcl hxBcl hf hAf hBf ?_ (Ne.symm hm)
    rw [hinter, segment_symm]
  have hseg_int : segment ℝ m₁ m₂ \ {m₁, m₂} ⊆ interior (A ∪ B) :=
    relint_subset_interior_union hAc hBc hAne hBne hf hAf hBf hinter hm
  have hInt : interior (A ∪ B)
      = interior A ∪ interior B ∪ (segment ℝ m₁ m₂ \ {m₁, m₂}) := by
    apply Subset.antisymm
    · intro w hwint
      have hwAB : w ∈ A ∪ B := interior_subset hwint
      rcases hwAB with h | h
      · by_cases hwi : w ∈ interior A
        · exact Or.inl (Or.inl hwi)
        · have hwfr : w ∈ frontier A := by
            rw [hxAcl.frontier_eq]
            exact ⟨h, hwi⟩
          have hwB : w ∈ B := by
            rw [← hxBcl.closure_eq, Metric.mem_closure_iff]
            intro ε hε
            obtain ⟨ε₀, hε₀, hball₀⟩ : ∃ ε₀ > 0, ball w ε₀ ⊆ A ∪ B := by
              rw [mem_interior_iff_mem_nhds] at hwint
              exact Metric.mem_nhds_iff.mp hwint
            have hclA : w ∈ closure Aᶜ := by
              rw [frontier_eq_closure_inter_closure] at hwfr
              exact hwfr.2
            rw [Metric.mem_closure_iff] at hclA
            obtain ⟨v, hvA, hvε⟩ := hclA (min ε ε₀) (lt_min hε hε₀)
            refine ⟨v, ?_, lt_of_lt_of_le hvε (min_le_left _ _)⟩
            have hv1 : v ∈ A ∪ B := hball₀ (by
              rw [Metric.mem_ball, dist_comm]
              exact lt_of_lt_of_le hvε (min_le_right _ _))
            rcases hv1 with h' | h'
            · exact absurd h' hvA
            · exact h'
          have hwS : w ∈ segment ℝ m₁ m₂ := by
            have h1 : w ∈ A ∩ B := ⟨h, hwB⟩
            rwa [hinter] at h1
          refine Or.inr ⟨hwS, ?_⟩
          rintro (h' | h')
          · exact (fun hc => hxint (h' ▸ hc)) hwint
          · exact (fun hc => hyint (h' ▸ hc)) hwint
      · by_cases hwi : w ∈ interior B
        · exact Or.inl (Or.inr hwi)
        · have hwfr : w ∈ frontier B := by
            rw [hxBcl.frontier_eq]
            exact ⟨h, hwi⟩
          have hwA : w ∈ A := by
            rw [← hxAcl.closure_eq, Metric.mem_closure_iff]
            intro ε hε
            obtain ⟨ε₀, hε₀, hball₀⟩ : ∃ ε₀ > 0, ball w ε₀ ⊆ A ∪ B := by
              rw [mem_interior_iff_mem_nhds] at hwint
              exact Metric.mem_nhds_iff.mp hwint
            have hclB : w ∈ closure Bᶜ := by
              rw [frontier_eq_closure_inter_closure] at hwfr
              exact hwfr.2
            rw [Metric.mem_closure_iff] at hclB
            obtain ⟨v, hvB, hvε⟩ := hclB (min ε ε₀) (lt_min hε hε₀)
            refine ⟨v, ?_, lt_of_lt_of_le hvε (min_le_left _ _)⟩
            have hv1 : v ∈ A ∪ B := hball₀ (by
              rw [Metric.mem_ball, dist_comm]
              exact lt_of_lt_of_le hvε (min_le_right _ _))
            rcases hv1 with h' | h'
            · exact h'
            · exact absurd h' hvB
          have hwS : w ∈ segment ℝ m₁ m₂ := by
            have h1 : w ∈ A ∩ B := ⟨hwA, h⟩
            rwa [hinter] at h1
          refine Or.inr ⟨hwS, ?_⟩
          rintro (h' | h')
          · exact (fun hc => hxint (h' ▸ hc)) hwint
          · exact (fun hc => hyint (h' ▸ hc)) hwint
    · intro w hw
      rcases hw with (h | h) | h
      · exact interior_mono subset_union_left h
      · exact interior_mono subset_union_right h
      · exact hseg_int h
  have hcl : IsClosed (A ∪ B) := hxAcl.union hxBcl
  rw [hcl.frontier_eq, hInt]
  ext w
  constructor
  · intro hw
    obtain ⟨hwAB, hwnot⟩ := hw
    rcases hwAB with h | h
    · left
      refine ⟨?_, fun hS => hwnot (Or.inr hS)⟩
      rw [hxAcl.frontier_eq]
      exact ⟨h, fun h' => hwnot (Or.inl (Or.inl h'))⟩
    · right
      refine ⟨?_, fun hS => hwnot (Or.inr hS)⟩
      rw [hxBcl.frontier_eq]
      exact ⟨h, fun h' => hwnot (Or.inl (Or.inr h'))⟩
  · rintro (hw | hw)
    · obtain ⟨hwfr, hwdeg⟩ := hw
      have hwA : w ∈ A := by
        have h1 : w ∈ closure A := frontier_subset_closure hwfr
        rwa [hxAcl.closure_eq] at h1
      refine ⟨Or.inl hwA, ?_⟩
      intro hcon
      rcases hcon with (h | h) | h
      · rw [hxAcl.frontier_eq] at hwfr
        exact hwfr.2 h
      · have hwS : w ∈ segment ℝ m₁ m₂ := by
          have h1 : w ∈ A ∩ B := ⟨hwA, interior_subset h⟩
          rwa [hinter] at h1
        have hmem : w ∈ ({m₁, m₂} : Set ℂ) := by
          by_contra h'
          exact hwdeg ⟨hwS, h'⟩
        rcases hmem with h' | h'
        · exact hxint (h' ▸ interior_mono subset_union_right h)
        · exact hyint (h' ▸ interior_mono subset_union_right h)
      · exact hwdeg h
    · obtain ⟨hwfr, hwdeg⟩ := hw
      have hwB : w ∈ B := by
        have h1 : w ∈ closure B := frontier_subset_closure hwfr
        rwa [hxBcl.closure_eq] at h1
      refine ⟨Or.inr hwB, ?_⟩
      intro hcon
      rcases hcon with (h | h) | h
      · have hwS : w ∈ segment ℝ m₁ m₂ := by
          have h1 : w ∈ A ∩ B := ⟨interior_subset h, hwB⟩
          rwa [hinter] at h1
        have hmem : w ∈ ({m₁, m₂} : Set ℂ) := by
          by_contra h'
          exact hwdeg ⟨hwS, h'⟩
        rcases hmem with h' | h'
        · exact hxint (h' ▸ interior_mono subset_union_left h)
        · exact hyint (h' ▸ interior_mono subset_union_left h)
      · rw [hxBcl.frontier_eq] at hwfr
        exact hwfr.2 h
      · exact hwdeg h

end

end Work.Drive.Mono
