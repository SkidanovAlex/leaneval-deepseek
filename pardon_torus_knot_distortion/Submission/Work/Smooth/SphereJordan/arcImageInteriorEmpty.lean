import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The image of a continuous arc in the Riemann sphere has empty interior

Let `α : C(Icc 0 1, RiemannSphere)` be a continuous injective path in the Riemann sphere.
Its image is a *simple arc*: it is one-dimensional and cannot contain a planar disc.  This file
proves `interior (Set.range α) = ∅`.

The argument is the classical "three points of a triangle" argument, transported to the sphere.

Suppose `α '' Icc 0 1` contained a nonempty open set.  Being an open subset of the sphere it meets
the finite part `ℂ`, so `(↑) '' Metric.ball w ε ⊆ Set.range α` for some `w : ℂ`, `ε > 0`.  The
three points `w`, `w + s`, `w + s * I` (with `s = ε/2`) of the ball form a non-degenerate triangle.
Their (pairwise distinct) parameters split `Icc 0 1`; order the three parameters, and let `tp` be
the middle one.  The compact pieces `α '' Icc 0 tp` and `α '' Icc tp 1` cover the image, meet
exactly in `α tp`, and are closed.  The segment in the ball joining the images of the two outer
parameters is a connected set contained in the image and avoiding `α tp`, so it must lie in one of
the two closed pieces — but it meets both.  Contradiction.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-! ## The clipped extension of a map defined on `[0,1]` -/

/-- The projection `ℝ → [0,1]` onto the unit interval. -/
private abbrev clip : ℝ → Set.Icc (0 : ℝ) 1 := Set.projIcc (0 : ℝ) 1 zero_le_one

private lemma continuous_clip : Continuous clip := by
  show Continuous (fun t : ℝ => Set.projIcc (0 : ℝ) 1 zero_le_one t)
  fun_prop

private lemma clip_eq_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clip t = ⟨t, ht⟩ :=
  Set.projIcc_of_mem zero_le_one ht

/-- The extension of `α` to all of `ℝ` by clipping the argument to `[0,1]`.  Its range is the
range of `α`, and it is injective on `Icc 0 1` as soon as `α` is injective. -/
private def arcExt (α : C(Set.Icc (0 : ℝ) 1, RiemannSphere)) (t : ℝ) : RiemannSphere :=
  α (clip t)

private lemma continuous_arcExt (α : C(Set.Icc (0 : ℝ) 1, RiemannSphere)) :
    Continuous (arcExt α) :=
  α.continuous.comp continuous_clip

private lemma arcExt_image_Icc (α : C(Set.Icc (0 : ℝ) 1, RiemannSphere)) :
    arcExt α '' Set.Icc (0 : ℝ) 1 = Set.range α := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, by
      rw [show arcExt α t = α (clip t) from rfl, clip_eq_of_mem ht]⟩
  · rintro y ⟨u, rfl⟩
    exact ⟨u.val, u.property, by
      rw [show arcExt α u.val = α (clip u.val) from rfl, clip_eq_of_mem u.property]⟩

private lemma injOn_arcExt {α : C(Set.Icc (0 : ℝ) 1, RiemannSphere)}
    (hα : Function.Injective α) : Set.InjOn (arcExt α) (Set.Icc (0 : ℝ) 1) := by
  intro t ht u hu h
  change α (clip t) = α (clip u) at h
  have h1 : clip t = clip u := hα h
  rw [clip_eq_of_mem ht, clip_eq_of_mem hu] at h1
  exact Subtype.ext_iff.mp h1

/-! ## Non-degeneracy of the model triangle `w, w + s, w + s * I` -/

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

/-- A coerced point lies in the coerced image of a segment iff the point lies in the segment. -/
private lemma coe_notMem_image_segment {c : ℂ} {zi zj : ℂ}
    (h : c ∉ segment ℝ zi zj) :
    ((c : ℂ) : RiemannSphere) ∉ ((↑) : ℂ → RiemannSphere) '' segment ℝ zi zj := by
  rintro ⟨v, hv, hvx⟩
  exact h (OnePoint.coe_eq_coe.mp hvx ▸ hv)

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

/-! ## The counting contradiction -/

/-- **The counting contradiction.**  If a preconnected set `S` contained in the image of `f` on
`Icc a b` contains the image of a parameter `ti < tp` and the image of a parameter `tj > tp`, and
avoids `f tp`, then `false`: the two compact pieces `f '' Icc a tp` and `f '' Icc tp b` cover
`f '' Icc a b`, are closed, meet only in `f tp`, and `S` would have to lie in one of them. -/
private lemma no_config {f : ℝ → RiemannSphere} {a b : ℝ} {S : Set RiemannSphere}
    (hf : Continuous f) (hinj : Set.InjOn f (Set.Icc a b))
    (hSsub : S ⊆ f '' Set.Icc a b) (hSpre : IsPreconnected S)
    (tp ti tj : ℝ) (zi zj : RiemannSphere)
    (htp : tp ∈ Set.Icc a b) (hti : ti ∈ Set.Icc a b) (htj : tj ∈ Set.Icc a b)
    (hit : ti < tp) (htj' : tp < tj)
    (hfi : f ti = zi) (hfj : f tj = zj)
    (hziS : zi ∈ S) (hzjS : zj ∈ S) (hoff : f tp ∉ S) : False := by
  have hIclosed : IsClosed (f '' Set.Icc a tp) := (isCompact_Icc.image hf).isClosed
  have hJclosed : IsClosed (f '' Set.Icc tp b) := (isCompact_Icc.image hf).isClosed
  have hcover : S ⊆ f '' Set.Icc a tp ∪ f '' Set.Icc tp b := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hSsub hx
    rcases le_total t tp with hle | hle
    · exact Or.inl ⟨t, ⟨ht.1, hle⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨hle, ht.2⟩, rfl⟩
  have hdisj : S ∩ (f '' Set.Icc a tp ∩ f '' Set.Icc tp b) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxS, hxI, hxJ⟩
    simp only [Set.mem_image, Set.mem_Icc] at hxI hxJ
    obtain ⟨u, ⟨hua, hutp⟩, hu'⟩ := hxI
    obtain ⟨v, ⟨hvtp, hvb⟩, hv'⟩ := hxJ
    have huab : u ∈ Set.Icc a b := ⟨hua, le_trans hutp htp.2⟩
    have hvab : v ∈ Set.Icc a b := ⟨le_trans htp.1 hvtp, hvb⟩
    have huv : u = v := hinj huab hvab (by rw [hu', hv'])
    have hup : u = tp := le_antisymm hutp (huv ▸ hvtp)
    have hxzp : x = f tp := by rw [← hu', hup]
    exact hoff (hxzp ▸ hxS)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hSpre _ _
      hIclosed hJclosed hcover hdisj) with hsub | hsub
  · have hmem : zj ∈ f '' Set.Icc a tp := hsub hzjS
    obtain ⟨u, hu, hu'⟩ := hmem
    have huab : u ∈ Set.Icc a b := ⟨hu.1, le_trans hu.2 htp.2⟩
    have hueq : u = tj := hinj huab htj (by rw [hu', hfj])
    have : tj ≤ tp := hueq ▸ hu.2
    exact absurd this (not_le.mpr htj')
  · have hmem : zi ∈ f '' Set.Icc tp b := hsub hziS
    obtain ⟨u, hu, hu'⟩ := hmem
    have huab : u ∈ Set.Icc a b := ⟨le_trans htp.1 hu.1, hu.2⟩
    have hueq : u = ti := hinj huab hti (by rw [hu', hfi])
    have : tp ≤ ti := hueq ▸ hu.1
    exact absurd this (not_le.mpr hit)

/-- The counting contradiction in the form used below: the preconnected set is the image in the
sphere of a planar segment contained in the chart ball `ball w ε`. -/
private lemma no_config_ball {f : ℝ → RiemannSphere} {w : ℂ} {ε : ℝ}
    (hf : Continuous f) (hinj : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hball : ((↑) : ℂ → RiemannSphere) '' Metric.ball w ε ⊆ f '' Set.Icc (0 : ℝ) 1)
    (tp ti tj : ℝ) (zi zj : ℂ)
    (htp : tp ∈ Set.Icc (0 : ℝ) 1) (hti : ti ∈ Set.Icc (0 : ℝ) 1) (htj : tj ∈ Set.Icc (0 : ℝ) 1)
    (hit : ti < tp) (htj' : tp < tj)
    (hfi : f ti = ((zi : ℂ) : RiemannSphere)) (hfj : f tj = ((zj : ℂ) : RiemannSphere))
    (hzi : zi ∈ Metric.ball w ε) (hzj : zj ∈ Metric.ball w ε)
    (hoff : f tp ∉ ((↑) : ℂ → RiemannSphere) '' segment ℝ zi zj) : False := by
  refine no_config (S := ((↑) : ℂ → RiemannSphere) '' segment ℝ zi zj) hf hinj ?_ ?_
    tp ti tj ((zi : ℂ) : RiemannSphere) ((zj : ℂ) : RiemannSphere) htp hti htj hit htj' hfi hfj ?_ ?_ hoff
  · exact (Set.image_mono ((convex_ball w ε).segment_subset hzi hzj)).trans hball
  · exact ((convex_segment zi zj).isPreconnected).image ((↑) : ℂ → RiemannSphere)
      OnePoint.continuous_coe.continuousOn
  · exact Set.mem_image_of_mem _ (left_mem_segment ℝ zi zj)
  · exact Set.mem_image_of_mem _ (right_mem_segment ℝ zi zj)

/-! ## The main theorem -/

theorem arcImageInteriorEmpty {α : C(Set.Icc (0 : ℝ) 1, RiemannSphere)}
    (hα : Function.Injective α) : interior (Set.range α) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  -- an interior point of the finite part of the sphere
  have hfin : ∃ w : ℂ, (w : RiemannSphere) ∈ interior (Set.range α) := by
    by_contra h
    push Not at h
    have hsubset : interior (Set.range α) ⊆ ({infty} : Set RiemannSphere) := by
      intro x hx
      by_contra hx'
      have hxr : x ∈ Set.range ((↑) : ℂ → RiemannSphere) := by
        rw [← OnePoint.compl_infty]; exact hx'
      obtain ⟨w, hw⟩ := hxr
      exact h w (hw ▸ hx)
    have hmeminf : infty ∈ interior (Set.range α) := by
      by_cases hy' : y = infty
      · exact hy' ▸ hy
      · obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hy'
        exact absurd (hw ▸ hy) (h w)
    have hsingle : interior (Set.range α) = {infty} :=
      le_antisymm hsubset (Set.singleton_subset_iff.mpr hmeminf)
    have hopen : IsOpen ({infty} : Set RiemannSphere) := hsingle ▸ isOpen_interior
    have hclosed : IsClosed (Set.range ((↑) : ℂ → RiemannSphere)) := by
      rw [← OnePoint.compl_infty]; exact hopen.isClosed_compl
    have hmem : infty ∈ closure (Set.range ((↑) : ℂ → RiemannSphere)) := by
      rw [OnePoint.denseRange_coe.closure_eq]; trivial
    rw [hclosed.closure_eq] at hmem
    exact OnePoint.infty_notMem_range_coe hmem
  obtain ⟨w, hw⟩ := hfin
  obtain ⟨ε, hε, hεball⟩ :=
    Metric.mem_nhds_iff.mp ((isOpen_interior.preimage OnePoint.continuous_coe).mem_nhds hw)
  have hball : ((↑) : ℂ → RiemannSphere) '' Metric.ball w ε ⊆ Set.range α := by
    rintro x ⟨v, hv, rfl⟩
    exact interior_subset (hεball hv)
  -- the three points of a non-degenerate triangle inside the ball
  set s : ℝ := ε / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hmem_w : w ∈ Metric.ball w ε := by rw [Metric.mem_ball, dist_self]; exact hε
  have hmem_p2 : w + (s : ℂ) ∈ Metric.ball w ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖(w + (s : ℂ)) - w‖ = |s| := by simp
    rw [this, abs_of_pos hs, hsdef]
    linarith
  have hmem_p3 : w + (s : ℂ) * Complex.I ∈ Metric.ball w ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖(w + (s : ℂ) * Complex.I) - w‖ = |s| := by simp
    rw [this, abs_of_pos hs, hsdef]
    linarith
  -- preimages of the three points, inside `[0,1]`
  obtain ⟨u1, hu1⟩ : ∃ u : Set.Icc (0 : ℝ) 1, α u = ((w : ℂ) : RiemannSphere) :=
    hball ⟨w, hmem_w, rfl⟩
  obtain ⟨u2, hu2⟩ :
      ∃ u : Set.Icc (0 : ℝ) 1, α u = (((w + (s : ℂ)) : ℂ) : RiemannSphere) :=
    hball ⟨w + (s : ℂ), hmem_p2, rfl⟩
  obtain ⟨u3, hu3⟩ :
      ∃ u : Set.Icc (0 : ℝ) 1, α u = (((w + (s : ℂ) * Complex.I) : ℂ) : RiemannSphere) :=
    hball ⟨w + (s : ℂ) * Complex.I, hmem_p3, rfl⟩
  have ha1 : arcExt α u1.val = ((w : ℂ) : RiemannSphere) := by
    change α (clip u1.val) = _; rw [clip_eq_of_mem u1.property]; exact hu1
  have ha2 : arcExt α u2.val = (((w + (s : ℂ)) : ℂ) : RiemannSphere) := by
    change α (clip u2.val) = _; rw [clip_eq_of_mem u2.property]; exact hu2
  have ha3 : arcExt α u3.val = (((w + (s : ℂ) * Complex.I) : ℂ) : RiemannSphere) := by
    change α (clip u3.val) = _; rw [clip_eq_of_mem u3.property]; exact hu3
  -- the three parameters are pairwise distinct
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hne12 : u1.val ≠ u2.val := by
    intro hh
    have hEq : ((w : ℂ) : RiemannSphere) = (((w + (s : ℂ)) : ℂ) : RiemannSphere) := by
      rw [← ha1, ← ha2, hh]
    have hw2 : w = w + (s : ℂ) := OnePoint.coe_eq_coe.mp hEq
    have hs0 : s = 0 := by
      have h := congrArg Complex.re hw2
      simp at h
      linarith
    exact hs_ne hs0
  have hne13 : u1.val ≠ u3.val := by
    intro hh
    have hEq : ((w : ℂ) : RiemannSphere) =
        (((w + (s : ℂ) * Complex.I) : ℂ) : RiemannSphere) := by
      rw [← ha1, ← ha3, hh]
    have hw3 : w = w + (s : ℂ) * Complex.I := OnePoint.coe_eq_coe.mp hEq
    have hs0 : s = 0 := by
      have h := congrArg Complex.im hw3
      simp at h
      linarith
    exact hs_ne hs0
  have hne23 : u2.val ≠ u3.val := by
    intro hh
    have hEq : (((w + (s : ℂ)) : ℂ) : RiemannSphere) =
        (((w + (s : ℂ) * Complex.I) : ℂ) : RiemannSphere) := by
      rw [← ha2, ← ha3, hh]
    have hw3 : w + (s : ℂ) = w + (s : ℂ) * Complex.I := OnePoint.coe_eq_coe.mp hEq
    have hs0 : s = 0 := by
      have h := congrArg Complex.re hw3
      simp at h
      linarith
    exact hs_ne hs0
  have hball' : ((↑) : ℂ → RiemannSphere) '' Metric.ball w ε ⊆ arcExt α '' Set.Icc (0 : ℝ) 1 := by
    rw [arcExt_image_Icc α]; exact hball
  rcases three_order hne12 hne13 hne23 with h | h | h | h | h | h
  · exact no_config_ball (continuous_arcExt α) (injOn_arcExt hα) hball'
      u2.val u1.val u3.val w (w + (s : ℂ) * Complex.I)
      u2.property u1.property u3.property h.1 h.2 ha1 ha3 hmem_w hmem_p3
      (by rw [ha2]; exact coe_notMem_image_segment (not_mem_seg2 w hs))
  · exact no_config_ball (continuous_arcExt α) (injOn_arcExt hα) hball'
      u3.val u1.val u2.val w (w + (s : ℂ))
      u3.property u1.property u2.property h.1 h.2 ha1 ha2 hmem_w hmem_p2
      (by rw [ha3]; exact coe_notMem_image_segment (not_mem_seg3 w hs))
  · exact no_config_ball (continuous_arcExt α) (injOn_arcExt hα) hball'
      u1.val u2.val u3.val (w + (s : ℂ)) (w + (s : ℂ) * Complex.I)
      u1.property u2.property u3.property h.1 h.2 ha2 ha3 hmem_p2 hmem_p3
      (by rw [ha1]; exact coe_notMem_image_segment (not_mem_seg1 w hs))
  · exact no_config_ball (continuous_arcExt α) (injOn_arcExt hα) hball'
      u3.val u2.val u1.val (w + (s : ℂ)) w
      u3.property u2.property u1.property h.1 h.2 ha2 ha1 hmem_p2 hmem_w
      (by rw [ha3];
          exact coe_notMem_image_segment (by rw [segment_symm]; exact not_mem_seg3 w hs))
  · exact no_config_ball (continuous_arcExt α) (injOn_arcExt hα) hball'
      u1.val u3.val u2.val (w + (s : ℂ) * Complex.I) (w + (s : ℂ))
      u1.property u3.property u2.property h.1 h.2 ha3 ha2 hmem_p3 hmem_p2
      (by rw [ha1];
          exact coe_notMem_image_segment (by rw [segment_symm]; exact not_mem_seg1 w hs))
  · exact no_config_ball (continuous_arcExt α) (injOn_arcExt hα) hball'
      u2.val u3.val u1.val (w + (s : ℂ) * Complex.I) w
      u2.property u3.property u1.property h.1 h.2 ha3 ha1 hmem_p3 hmem_w
      (by rw [ha2];
          exact coe_notMem_image_segment (by rw [segment_symm]; exact not_mem_seg2 w hs))

end

end Work.Smooth.SphereJordan
