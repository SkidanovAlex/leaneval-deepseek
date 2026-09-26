import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The trace of a simple closed curve on the Riemann sphere has empty interior

A simple closed curve of the Riemann sphere `ℂ ∪ {∞}` is a one-dimensional object and cannot
contain a planar disc.  This file proves the precise statement needed by the sibling chapter
(`curve_misses_point`),

`interior (Set.range c) = ∅` for `c` a simple closed curve of `ℂ ∪ {∞}`,

from scratch, in the elementary "triangle" style (no Jordan curve theorem and no invariance of
domain is used).

The proof: suppose the trace of `c` contains a point of its own interior; then (the interior being
open, and its preimage under `ℂ → ℂ ∪ {∞}` being open in `ℂ`) it contains a disc.  Shrinking that
disc a little we may even assume that `c 0` is not in it.  The three points

`z₁ = y`, `z₂ = y + r/2`, `z₃ = y + r/2 * I`

of `B` form a non-degenerate triangle.  Each `zᵢ` has a preimage `tᵢ ∈ [0, 2π)`; the three are
pairwise distinct, so one of them, say `tₚ`, lies strictly between the other two, `tᵢ < tₚ < tⱼ`.
The compact pieces `c '' [0, tₚ]` and `c '' [tₚ, 2π]` are closed, cover the trace of `c`, and meet
exactly in `{c 0, c tₚ} = {c 0, ↑zₚ}`.  The segment `[zᵢ, zⱼ]` (doubled by convexity of the disc,
hence contained in the trace) avoids the pivot `zₚ` (the triangle is non-degenerate) and avoids
`c 0` (by the choice of the disc), so it is a preconnected set inside the union of the two closed
pieces meeting neither of the two intersection points; hence it lies in one of them.  But its two
endpoints `zᵢ` and `zⱼ` map to the two different pieces, contradicting injectivity of `c` on one
period.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-! ## Elementary parameter lemmas -/

/-- Every point of the range of a `2π`-periodic map has a preimage in the half-open period
`[0, 2π)`. -/
private lemma exists_preimage_Ico {c : ℝ → RiemannSphere}
    (hper : Function.Periodic c (2 * Real.pi)) {x : RiemannSphere} (hx : x ∈ Set.range c) :
    ∃ t ∈ Set.Ico 0 (2 * Real.pi), c t = x := by
  rw [← hper.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi) 0] at hx
  obtain ⟨t, ht, htx⟩ := hx
  rcases eq_or_lt_of_le ht.2 with h | h
  · refine ⟨0, ⟨le_refl _, by positivity⟩, ?_⟩
    rw [← htx, h]
    exact (hper 0).symm
  · exact ⟨t, ⟨ht.1, by simpa using h⟩, htx⟩

/-- The six possible orders of three pairwise distinct reals, arranged so that in each disjunct the
first and the last are the outer ones and the middle one is the *middle* element. -/
private lemma three_order {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨ (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
      (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by
  rcases lt_trichotomy a b with hab' | hab' | hab'
  · rcases lt_trichotomy b c with hbc' | hbc' | hbc'
    · exact Or.inl ⟨hab', hbc'⟩
    · exact absurd hbc' hbc
    · rcases lt_trichotomy a c with hac' | hac' | hac'
      · exact Or.inr (Or.inl ⟨hac', hbc'⟩)
      · exact absurd hac' hac
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hac', hab'⟩))))
  · exact absurd hab' hab
  · rcases lt_trichotomy a c with hac' | hac' | hac'
    · exact Or.inr (Or.inr (Or.inl ⟨hab', hac'⟩))
    · exact absurd hac' hac
    · rcases lt_trichotomy b c with hbc' | hbc' | hbc'
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc', hac'⟩)))
      · exact absurd hbc' hbc
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbc', hab'⟩))))

/-! ## Non-degeneracy of the model triangle `y, y + s, y + s * I` -/

private lemma not_mem_segment_aux1 (y : ℂ) {s : ℝ} (hs : 0 < s) :
    y ∉ segment ℝ (y + (s : ℂ)) (y + (s : ℂ) * Complex.I) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨θ, _, hθeq⟩ := h
  have hre := congrArg Complex.re hθeq
  have him := congrArg Complex.im hθeq
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    smul_eq_mul, mul_zero, mul_one, add_zero] at hre him
  ring_nf at hre him
  nlinarith [hre, him, hs]

private lemma not_mem_segment_aux2 (y : ℂ) {s : ℝ} (hs : 0 < s) :
    (y + (s : ℂ)) ∉ segment ℝ y (y + (s : ℂ) * Complex.I) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨θ, _, hθeq⟩ := h
  have hre := congrArg Complex.re hθeq
  simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    smul_eq_mul, mul_zero] at hre
  ring_nf at hre
  nlinarith [hre, hs]

private lemma not_mem_segment_aux3 (y : ℂ) {s : ℝ} (hs : 0 < s) :
    (y + (s : ℂ) * Complex.I) ∉ segment ℝ y (y + (s : ℂ)) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨θ, _, hθeq⟩ := h
  have him := congrArg Complex.im hθeq
  simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    smul_eq_mul, sub_self, mul_zero, mul_one, add_zero] at him
  ring_nf at him
  nlinarith [him, hs]

/-! ## The separation step -/

/-- **The counting contradiction.**  If a convex set `B`, contained in the trace of a `2π`-periodic
injective-on-a-period curve `c`, carries three points with preimages `tᵢ < tₚ < tⱼ`, and the segment
joining the two outer points avoids the pivot point `↑zₚ = c tₚ` and the seam point `c 0`, then we
get a contradiction: the compact pieces `c '' [0, tₚ]` and `c '' [tₚ, 2π]` cover the trace, meet
exactly in `{c 0, c tₚ}`, and the preconnected segment would have to lie in one of them while its
two endpoints map to the two different pieces. -/
private lemma no_config {c : ℝ → RiemannSphere} (hcont : Continuous c)
    (hper : Function.Periodic c (2 * Real.pi))
    (hinj : Set.InjOn c (Set.Ico 0 (2 * Real.pi)))
    {B : Set ℂ} (hB : (↑) '' B ⊆ Set.range c) (hBc : Convex ℝ B)
    (h0 : c 0 ∉ (↑) '' B)
    {ti tp tj : ℝ} {zi zp zj : ℂ}
    (hti : ti ∈ Set.Ico 0 (2 * Real.pi)) (htp : tp ∈ Set.Ico 0 (2 * Real.pi))
    (htj : tj ∈ Set.Ico 0 (2 * Real.pi))
    (hit : ti < tp) (htj' : tp < tj)
    (hzi : c ti = ↑zi) (hzp : c tp = ↑zp) (hzj : c tj = ↑zj)
    (hziB : zi ∈ B) (hzjB : zj ∈ B)
    (hoff : zp ∉ segment ℝ zi zj) : False := by
  have hA1 : IsClosed (c '' Set.Icc 0 tp) := (isCompact_Icc.image hcont).isClosed
  have hA2 : IsClosed (c '' Set.Icc tp (2 * Real.pi)) := (isCompact_Icc.image hcont).isClosed
  have hsegB : segment ℝ zi zj ⊆ B := hBc.segment_subset hziB hzjB
  have hpre : IsPreconnected ((↑) '' segment ℝ zi zj : Set RiemannSphere) :=
    (convex_segment zi zj).isPreconnected.image OnePoint.some OnePoint.continuous_coe.continuousOn
  have hcover : (↑) '' segment ℝ zi zj ⊆
      c '' Set.Icc 0 tp ∪ c '' Set.Icc tp (2 * Real.pi) := by
    rw [Set.image_subset_iff]
    intro z hz
    have hzB : (↑z : RiemannSphere) ∈ Set.range c := hB ⟨z, hsegB hz, rfl⟩
    rw [← hper.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi) 0] at hzB
    obtain ⟨u, hu, huc⟩ := hzB
    have hu' : u ≤ 2 * Real.pi := by simpa using hu.2
    rcases le_total u tp with hle | hle
    · exact Or.inl ⟨u, ⟨hu.1, hle⟩, huc⟩
    · exact Or.inr ⟨u, ⟨hle, hu'⟩, huc⟩
  have hdisj : ((↑) '' segment ℝ zi zj) ∩
      (c '' Set.Icc 0 tp ∩ c '' Set.Icc tp (2 * Real.pi)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨z, hz, hzx⟩, ⟨⟨u, hu, hux⟩, ⟨v, hv, hvx⟩⟩⟩
    simp only [Set.mem_Icc] at hu hv
    have hzu : c u = ↑z := hux.trans hzx.symm
    have hzv : c v = ↑z := hvx.trans hzx.symm
    have hz0 : (↑z : RiemannSphere) ≠ c 0 := by
      intro heq
      exact h0 ⟨z, hsegB hz, heq⟩
    have hv2 : v < 2 * Real.pi := by
      rcases lt_or_eq_of_le hv.2 with h | h
      · exact h
      · exfalso
        have hvc : (↑z : RiemannSphere) = c 0 := by
          rw [← hzv, h]
          simpa using (hper 0)
        exact hz0 hvc
    have hu2 : u < 2 * Real.pi := lt_of_le_of_lt hu.2 htp.2
    have huv : u = v := hinj ⟨hu.1, hu2⟩ ⟨le_trans htp.1 hv.1, hv2⟩ (by rw [hzu, hzv])
    have hup : u = tp := le_antisymm hu.2 (huv ▸ hv.1)
    have hz_eq : z = zp := OnePoint.coe_injective (by rw [← hzu, hup, hzp])
    exact hoff (hz_eq ▸ hz)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hpre _ _ hA1 hA2 hcover hdisj with
    hsub1 | hsub2
  · have hzjA1 : (↑zj : RiemannSphere) ∈ c '' Set.Icc 0 tp :=
      hsub1 ⟨zj, right_mem_segment ℝ zi zj, rfl⟩
    obtain ⟨u, hu, huc⟩ := hzjA1
    simp only [Set.mem_Icc] at hu
    have hu2 : u < 2 * Real.pi := lt_of_le_of_lt hu.2 htp.2
    have hueq : u = tj := hinj ⟨hu.1, hu2⟩ htj (by rw [huc, hzj])
    linarith [hu.2, hueq, htj']
  · have hziA2 : (↑zi : RiemannSphere) ∈ c '' Set.Icc tp (2 * Real.pi) :=
      hsub2 ⟨zi, left_mem_segment ℝ zi zj, rfl⟩
    obtain ⟨v, hv, hvc⟩ := hziA2
    simp only [Set.mem_Icc] at hv
    have hv2 : v < 2 * Real.pi := by
      rcases lt_or_eq_of_le hv.2 with h | h
      · exact h
      · exfalso
        have hv0 : (↑zi : RiemannSphere) = c 0 := by
          rw [← hvc, h]
          simpa using (hper 0)
        exact h0 ⟨zi, hziB, hv0⟩
    have veq : v = ti := hinj ⟨le_trans htp.1 hv.1, hv2⟩ hti (by rw [hvc, hzi])
    linarith [hv.1, veq, hit]

/-! ## No disc is contained in the trace of the curve -/

/-- No planar disc is contained in the trace of a `2π`-periodic curve that is injective on one
period, as soon as the disc avoids the seam point `c 0`. -/
private lemma no_ball_subset_range {c : ℝ → RiemannSphere} (hcont : Continuous c)
    (hper : Function.Periodic c (2 * Real.pi))
    (hinj : Set.InjOn c (Set.Ico 0 (2 * Real.pi)))
    {y : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : (↑) '' Metric.ball y r ⊆ Set.range c)
    (h0 : c 0 ∉ (↑) '' Metric.ball y r) : False := by
  set s : ℝ := r / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  set B : Set ℂ := Metric.ball y r with hBdef
  have hBc : Convex ℝ B := convex_ball y r
  have hBsub : (↑) '' B ⊆ Set.range c := hsub
  set z1 : ℂ := y with hz1def
  set z2 : ℂ := y + (s : ℂ) with hz2def
  set z3 : ℂ := y + (s : ℂ) * Complex.I with hz3def
  have hz1B : z1 ∈ B := by
    rw [hBdef, hz1def, Metric.mem_ball, dist_self]
    exact hr
  have hz2B : z2 ∈ B := by
    rw [hBdef, hz2def, Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖y + (s : ℂ) - y‖ = |s| := by simp
    rw [hnorm, abs_of_pos hs, hsdef]
    linarith
  have hz3B : z3 ∈ B := by
    rw [hBdef, hz3def, Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖y + (s : ℂ) * Complex.I - y‖ = |s| := by simp
    rw [hnorm, abs_of_pos hs, hsdef]
    linarith
  obtain ⟨t1, ht1, hc1⟩ := exists_preimage_Ico hper (hBsub ⟨z1, hz1B, rfl⟩)
  obtain ⟨t2, ht2, hc2⟩ := exists_preimage_Ico hper (hBsub ⟨z2, hz2B, rfl⟩)
  obtain ⟨t3, ht3, hc3⟩ := exists_preimage_Ico hper (hBsub ⟨z3, hz3B, rfl⟩)
  have hnc1 : z1 ∉ segment ℝ z2 z3 := by
    rw [hz1def, hz2def, hz3def]
    exact not_mem_segment_aux1 y hs
  have hnc2 : z2 ∉ segment ℝ z1 z3 := by
    rw [hz1def, hz2def, hz3def]
    exact not_mem_segment_aux2 y hs
  have hnc3 : z3 ∉ segment ℝ z1 z2 := by
    rw [hz1def, hz2def, hz3def]
    exact not_mem_segment_aux3 y hs
  have ht12 : t1 ≠ t2 := by
    intro heq
    have hz : z1 = z2 := OnePoint.coe_injective (by rw [← hc1, ← hc2, heq])
    rw [hz1def, hz2def] at hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  have ht13 : t1 ≠ t3 := by
    intro heq
    have hz : z1 = z3 := OnePoint.coe_injective (by rw [← hc1, ← hc3, heq])
    rw [hz1def, hz3def] at hz
    have him := congrArg Complex.im hz
    simp at him
    linarith
  have ht23 : t2 ≠ t3 := by
    intro heq
    have hz : z2 = z3 := OnePoint.coe_injective (by rw [← hc2, ← hc3, heq])
    rw [hz2def, hz3def] at hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  rcases three_order ht12 ht13 ht23 with h | h | h | h | h | h
  · exact no_config hcont hper hinj hBsub hBc h0 ht1 ht2 ht3 h.1 h.2 hc1 hc2 hc3 hz1B hz3B hnc2
  · exact no_config hcont hper hinj hBsub hBc h0 ht1 ht3 ht2 h.1 h.2 hc1 hc3 hc2 hz1B hz2B hnc3
  · exact no_config hcont hper hinj hBsub hBc h0 ht2 ht1 ht3 h.1 h.2 hc2 hc1 hc3 hz2B hz3B hnc1
  · exact no_config hcont hper hinj hBsub hBc h0 ht2 ht3 ht1 h.1 h.2 hc2 hc3 hc1 hz2B hz1B
      (by rw [segment_symm]; exact hnc3)
  · exact no_config hcont hper hinj hBsub hBc h0 ht3 ht1 ht2 h.1 h.2 hc3 hc1 hc2 hz3B hz2B
      (by rw [segment_symm]; exact hnc1)
  · exact no_config hcont hper hinj hBsub hBc h0 ht3 ht2 ht1 h.1 h.2 hc3 hc2 hc1 hz3B hz1B
      (by rw [segment_symm]; exact hnc2)

/-! ## The main theorem -/

theorem interior_range_empty_of_isSimpleClosedCurve {c : ℝ → RiemannSphere}
    (hc : IsSimpleClosedCurve c) : interior (Set.range c) = ∅ := by
  obtain ⟨hcont, hper, hinj⟩ := hc
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hSopen : IsOpen ((↑) ⁻¹' (interior (Set.range c)) : Set ℂ) := by
    rw [← OnePoint.isOpen_image_coe, Set.image_preimage_eq_inter_range]
    exact isOpen_interior.inter OnePoint.isOpen_range_coe
  have hSne : ((↑) ⁻¹' (interior (Set.range c)) : Set ℂ).Nonempty := by
    by_cases hxinf : x = OnePoint.infty
    · have hx' : OnePoint.infty ∈ (interior (Set.range c)) := hxinf ▸ hx
      have hcpt : IsCompact (((↑) ⁻¹' (interior (Set.range c)))ᶜ : Set ℂ) :=
        ((OnePoint.isOpen_iff_of_mem' hx').mp isOpen_interior).1
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, compl_empty] at hcpt
      exact hcpt.ne_univ rfl
    · obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp hxinf
      refine ⟨y, ?_⟩
      show (y : RiemannSphere) ∈ interior (Set.range c)
      rw [hy]
      exact hx
  obtain ⟨y, hy⟩ := hSne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hSopen y hy
  have hsub : (↑) '' Metric.ball y r ⊆ Set.range c := by
    rintro _ ⟨z, hz, rfl⟩
    exact interior_subset (hball hz)
  by_cases h0 : c 0 ∈ (↑) '' Metric.ball y r
  · obtain ⟨z₀, hz₀mem, hz₀eq⟩ := h0
    have hne : ∃ y' ∈ Metric.ball y r, y' ≠ z₀ := by
      by_cases hyz : y = z₀
      · refine ⟨y + (r / 2 : ℝ), ?_, ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm]
          have hnorm : ‖y + (r / 2 : ℝ) - y‖ = |r| / 2 := by simp
          rw [hnorm, abs_of_pos hr]
          linarith
        · intro hcontra
          have hre := congrArg Complex.re hcontra
          rw [hyz] at hre
          simp at hre
          linarith
      · exact ⟨y, by rw [Metric.mem_ball, dist_self]; exact hr, hyz⟩
    obtain ⟨y', hy'mem, hy'ne⟩ := hne
    have hBopen : IsOpen (Metric.ball y r \ {z₀}) := Metric.isOpen_ball.sdiff isClosed_singleton
    obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.mp hBopen y' ⟨hy'mem, hy'ne⟩
    refine no_ball_subset_range (y := y') (r := r') hcont hper hinj hr' ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hsub ⟨z, (hball' hz).1, rfl⟩
    · rintro ⟨z, hz, hze⟩
      exact (hball' hz).2 (OnePoint.coe_injective (hze.trans hz₀eq.symm))
  · exact no_ball_subset_range (y := y) (r := r) hcont hper hinj hr hsub h0

end

end Work.Smooth.SphereJordan
