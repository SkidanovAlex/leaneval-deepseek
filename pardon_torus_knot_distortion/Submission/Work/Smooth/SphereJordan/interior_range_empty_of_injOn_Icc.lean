import Mathlib

/-!
# The image of a compact interval under an injective continuous map into `ℂ` has empty interior

A continuous injective map `f : ℝ → ℂ` restricted to a compact interval `[a, b]` is an embedding
(compact source, Hausdorff target), so `f '' [a, b]` is a *simple arc* in the plane.  A simple arc
has empty interior: it is one-dimensional, and cannot contain a planar disc.

The proof below is the classical triangle argument, carried out without any homeomorphism
machinery:

* supposing `w` is an interior point, some disc `ball w ρ` is contained in `f '' [a, b]`;
* the three points `w`, `w + ρ/2`, `w + ρ/2 * I` of that disc form a non-degenerate triangle; let
  `t₁, t₂, t₃ ∈ [a, b]` be their (pairwise distinct) preimages and order them;
* the middle one, say `t`, splits `f '' [a, b]` into the two compact pieces `f '' [a, t]` and
  `f '' [t, b]`, which meet only in `f t`.  The two outer points are joined by a segment lying in
  the disc, hence in `f '' [a, b]`, and that segment avoids the middle vertex (the triangle is
  non-degenerate);
* a preconnected set inside a union of two closed sets disjoint on it lies in one of them, but the
  segment meets both pieces — contradiction.

The statement (and the name) is exactly the one requested by the sibling chapter
`Work.Smooth.SphereJordan` (`curve_misses_point`), where it supplies the existence of a point off
a simple closed plane curve.
-/

namespace Work.Smooth.SphereJordan

open Set

/-! ## Non-degeneracy of the model triangle `c, c + s, c + s * I` -/

private lemma not_mem_seg1 (c : ℂ) {s : ℝ} (hs : 0 < s) :
    c ∉ segment ℝ (c + s) (c + s * Complex.I) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨θ, hθ, hθeq⟩ := h
  have hre := congrArg Complex.re hθeq
  have him := congrArg Complex.im hθeq
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    smul_eq_mul, mul_zero, mul_one, sub_zero, add_zero] at hre him
  ring_nf at hre him
  have him' : s * θ = 0 := by linarith
  have hre' : s * θ = s := by linarith
  nlinarith [hs]

private lemma not_mem_seg2 (c : ℂ) {s : ℝ} (hs : 0 < s) :
    (c + s) ∉ segment ℝ c (c + s * Complex.I) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨θ, hθ, hθeq⟩ := h
  have hre := congrArg Complex.re hθeq
  simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    smul_eq_mul, mul_zero] at hre
  ring_nf at hre
  linarith

private lemma not_mem_seg3 (c : ℂ) {s : ℝ} (hs : 0 < s) :
    (c + s * Complex.I) ∉ segment ℝ c (c + s) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨θ, hθ, hθeq⟩ := h
  have him := congrArg Complex.im hθeq
  simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    smul_eq_mul, sub_self, mul_zero, mul_one, add_zero] at him
  ring_nf at him
  linarith

/-! ## The separation step -/

/-- **The counting contradiction.** If a segment contained in `f '' [a, b]` (through a convex set
`B`) joins a point with preimage `tᵢ < tₚ` to a point with preimage `tⱼ > tₚ`, and avoids the pivot
point `f tₚ`, then we get a contradiction: the compact pieces `f '' [a, tₚ]` and `f '' [tₚ, b]` cover
`f '' [a, b]`, meet only in `f tₚ`, are closed, and the preconnected segment would have to lie in
one of them, but it meets both. -/
private lemma no_config {f : ℝ → ℂ} {a b : ℝ} {B : Set ℂ}
    (hf : Continuous f) (hinj : Set.InjOn f (Set.Icc a b))
    (hB : B ⊆ f '' Set.Icc a b) (hconv : Convex ℝ B)
    (tp ti tj : ℝ) (zp zi zj : ℂ)
    (htp : tp ∈ Set.Icc a b) (hti : ti ∈ Set.Icc a b) (htj : tj ∈ Set.Icc a b)
    (hit : ti < tp) (htj' : tp < tj)
    (hfp : f tp = zp) (hfi : f ti = zi) (hfj : f tj = zj)
    (hziB : zi ∈ B) (hzjB : zj ∈ B)
    (hoff : zp ∉ segment ℝ zi zj) : False := by
  have hIclosed : IsClosed (f '' Set.Icc a tp) := (isCompact_Icc.image hf).isClosed
  have hJclosed : IsClosed (f '' Set.Icc tp b) := (isCompact_Icc.image hf).isClosed
  have hcover : segment ℝ zi zj ⊆ f '' Set.Icc a tp ∪ f '' Set.Icc tp b := by
    intro x hx
    have hxB : x ∈ B := hconv.segment_subset hziB hzjB hx
    obtain ⟨t, ht, htx⟩ := hB hxB
    rcases le_total t tp with hle | hle
    · exact Or.inl ⟨t, ⟨ht.1, hle⟩, htx⟩
    · exact Or.inr ⟨t, ⟨hle, ht.2⟩, htx⟩
  have hdisj : segment ℝ zi zj ∩ (f '' Set.Icc a tp ∩ f '' Set.Icc tp b) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxS, hxI, hxJ⟩
    simp only [Set.mem_image, Set.mem_Icc] at hxI hxJ
    obtain ⟨u, ⟨hua, hutp⟩, hu'⟩ := hxI
    obtain ⟨v, ⟨hvtp, hvb⟩, hv'⟩ := hxJ
    have huab : u ∈ Set.Icc a b := ⟨hua, le_trans hutp htp.2⟩
    have hvab : v ∈ Set.Icc a b := ⟨le_trans htp.1 hvtp, hvb⟩
    have huv : u = v := hinj huab hvab (by rw [hu', hv'])
    have hup : u = tp := le_antisymm hutp (huv ▸ hvtp)
    have hxzp : x = zp := by rw [← hu', hup, hfp]
    exact hoff (hxzp ▸ hxS)
  have hpre : IsPreconnected (segment ℝ zi zj) := (convex_segment (𝕜 := ℝ) zi zj).isPreconnected
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre _ _
      hIclosed hJclosed hcover hdisj) with hsub | hsub
  · have hzjS : zj ∈ segment ℝ zi zj := right_mem_segment ℝ zi zj
    obtain ⟨u, hu, hu'⟩ := hsub hzjS
    have huab : u ∈ Set.Icc a b := ⟨hu.1, le_trans hu.2 htp.2⟩
    have hueq : u = tj := hinj huab htj (by rw [hu', hfj])
    linarith [hu.2, hueq]
  · have hziS : zi ∈ segment ℝ zi zj := left_mem_segment ℝ zi zj
    obtain ⟨u, hu, hu'⟩ := hsub hziS
    have huab : u ∈ Set.Icc a b := ⟨le_trans htp.1 hu.1, hu.2⟩
    have hueq : u = ti := hinj huab hti (by rw [hu', hfi])
    linarith [hu.1, hueq]

/-! ## Ordering three distinct reals -/

private lemma three_order {t1 t2 t3 : ℝ} (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3) :
    (t1 < t2 ∧ t2 < t3) ∨ (t1 < t3 ∧ t3 < t2) ∨ (t2 < t1 ∧ t1 < t3) ∨
    (t2 < t3 ∧ t3 < t1) ∨ (t3 < t1 ∧ t1 < t2) ∨ (t3 < t2 ∧ t2 < t1) := by
  rcases lt_trichotomy t1 t2 with h12' | h12' | h12'
  · rcases lt_trichotomy t2 t3 with h23' | h23' | h23'
    · exact Or.inl ⟨h12', h23'⟩
    · exact absurd h23' h23
    · rcases lt_trichotomy t1 t3 with h13' | h13' | h13'
      · exact Or.inr (Or.inl ⟨h13', h23'⟩)
      · exact absurd h13' h13
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h13', h12'⟩))))
  · exact absurd h12' h12
  · rcases lt_trichotomy t1 t3 with h13' | h13' | h13'
    · exact Or.inr (Or.inr (Or.inl ⟨h12', h13'⟩))
    · exact absurd h13' h13
    · rcases lt_trichotomy t2 t3 with h23' | h23' | h23'
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h23', h13'⟩)))
      · exact absurd h23' h23
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h23', h12'⟩))))

/-! ## The main theorem -/

theorem interior_range_empty_of_injOn_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hf : Continuous f)
    (hinj : Set.InjOn f (Set.Icc a b)) : interior (f '' Set.Icc a b) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  obtain ⟨ρ, hρ, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) w hw
  have hballK : Metric.ball w ρ ⊆ f '' Set.Icc a b := hball.trans interior_subset
  set s : ℝ := ρ / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hz1 : w ∈ Metric.ball w ρ := by rw [Metric.mem_ball, dist_self]; exact hρ
  have hz2 : w + (s : ℂ) ∈ Metric.ball w ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖(w + (s:ℂ)) - w‖ = |s| := by simp
    rw [this, abs_of_pos hs, hsdef]
    linarith
  have hz3 : w + (s : ℂ) * Complex.I ∈ Metric.ball w ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖(w + (s:ℂ) * Complex.I) - w‖ = |s| := by simp
    rw [this, abs_of_pos hs, hsdef]
    linarith
  obtain ⟨t1, ht1, hft1⟩ := hballK hz1
  obtain ⟨t2, ht2, hft2⟩ := hballK hz2
  obtain ⟨t3, ht3, hft3⟩ := hballK hz3
  have h12 : t1 ≠ t2 := by
    intro hh
    have hfeq : f t1 = f t2 := by rw [hh]
    rw [hft1, hft2] at hfeq
    have := congrArg Complex.re hfeq
    simp at this
    linarith [hs]
  have h13 : t1 ≠ t3 := by
    intro hh
    have hfeq : f t1 = f t3 := by rw [hh]
    rw [hft1, hft3] at hfeq
    have := congrArg Complex.im hfeq
    simp at this
    linarith [hs]
  have h23 : t2 ≠ t3 := by
    intro hh
    have hfeq : f t2 = f t3 := by rw [hh]
    rw [hft2, hft3] at hfeq
    have := congrArg Complex.re hfeq
    simp at this
    linarith [hs]
  have hoff1 := not_mem_seg1 w hs
  have hoff2 := not_mem_seg2 w hs
  have hoff3 := not_mem_seg3 w hs
  have hcv : Convex ℝ (Metric.ball w ρ) := convex_ball w ρ
  rcases three_order h12 h13 h23 with h | h | h | h | h | h
  · exact no_config hf hinj hballK hcv t2 t1 t3 (w + s) w (w + s * Complex.I)
      ht2 ht1 ht3 h.1 h.2 hft2 hft1 hft3 hz1 hz3 hoff2
  · exact no_config hf hinj hballK hcv t3 t1 t2 (w + s * Complex.I) w (w + s)
      ht3 ht1 ht2 h.1 h.2 hft3 hft1 hft2 hz1 hz2 hoff3
  · exact no_config hf hinj hballK hcv t1 t2 t3 w (w + s) (w + s * Complex.I)
      ht1 ht2 ht3 h.1 h.2 hft1 hft2 hft3 hz2 hz3 hoff1
  · exact no_config hf hinj hballK hcv t3 t2 t1 (w + s * Complex.I) (w + s) w
      ht3 ht2 ht1 h.1 h.2 hft3 hft2 hft1 hz2 hz1 (by rw [segment_symm]; exact hoff3)
  · exact no_config hf hinj hballK hcv t1 t3 t2 w (w + s * Complex.I) (w + s)
      ht1 ht3 ht2 h.1 h.2 hft1 hft3 hft2 hz3 hz2 (by rw [segment_symm]; exact hoff1)
  · exact no_config hf hinj hballK hcv t2 t3 t1 (w + s) (w + s * Complex.I) w
      ht2 ht3 ht1 h.1 h.2 hft2 hft3 hft1 hz3 hz1 (by rw [segment_symm]; exact hoff2)

end Work.Smooth.SphereJordan
