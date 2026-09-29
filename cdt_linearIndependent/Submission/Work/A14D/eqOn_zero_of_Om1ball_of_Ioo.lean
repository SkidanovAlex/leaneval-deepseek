import Mathlib
import Submission.Work.A14.defs

/-!
# `Work.A14D.eqOn_zero_of_Om1ball_of_Ioo`

Identity theorem for the slit disc `Metric.ball (1 : ℂ) δ ∩ Om1`, `Om1 = ℂ ∖ (−∞, 1]`.

If `f` is holomorphic on `Metric.ball (1 : ℂ) δ ∩ Om1` and vanishes on the real interval
`(1, 1 + ε)` with `0 < ε ≤ δ`, then `f` vanishes on the whole slit disc.  Indeed that set is
the open disc `ball (1 : ℂ) δ` with the real segment `[1 − δ, 1]` removed, hence preconnected;
the interval `(1, 1 + ε)` lies inside it and accumulates at its interior point `1 + ε/2`, so the
principle of isolated zeros applies.
-/

namespace Work.A14D

open Complex Metric Filter Set

/-- `Om1 = ℂ ∖ (−∞, 1]` is open. -/
lemma isOpen_Om1 : IsOpen Om1 := by
  have hset : Om1 = {z : ℂ | z.im ≠ 0} ∪ {z : ℂ | 1 < z.re} := rfl
  rw [hset]
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Membership in the disc `ball (1 : ℂ) δ` from bounds on `re − 1` and `im`. -/
private lemma mem_ball_one_of_re_im {δ : ℝ} {z : ℂ} (h : |z.re - 1| + |z.im| < δ) :
    z ∈ Metric.ball (1 : ℂ) δ := by
  rw [Metric.mem_ball, Complex.dist_eq]
  calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im (z - 1)
    _ = |z.re - 1| + |z.im| := by simp
    _ < δ := h

/-- The slit disc `Metric.ball (1 : ℂ) δ ∩ Om1` is preconnected for `δ > 0`: it is the union of
the three convex pieces cut out by `1 < Re`, `0 < Im` and `Im < 0`, glued along the two points
`1 + δ/4 ± i δ/4`. -/
lemma isPreconnected_ball_inter_Om1 {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected (Metric.ball (1 : ℂ) δ ∩ Om1) := by
  have hpos : (0 : ℝ) < δ / 4 := by linarith
  have hA : IsPreconnected (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 1 < z.re}) :=
    ((convex_ball (1 : ℂ) δ).inter (convex_halfSpace_re_gt 1)).isPreconnected
  have hB : IsPreconnected (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im}) :=
    ((convex_ball (1 : ℂ) δ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC : IsPreconnected (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0}) :=
    ((convex_ball (1 : ℂ) δ).inter (convex_halfSpace_im_lt 0)).isPreconnected
  -- the two glue points
  set p : ℂ := ((1 + δ / 4 : ℝ) : ℂ) + ((δ / 4 : ℝ) : ℂ) * Complex.I with hp
  set q : ℂ := ((1 + δ / 4 : ℝ) : ℂ) - ((δ / 4 : ℝ) : ℂ) * Complex.I with hq
  have hp_re : p.re = 1 + δ / 4 := by rw [hp]; simp
  have hp_im : p.im = δ / 4 := by rw [hp]; simp
  have hq_re : q.re = 1 + δ / 4 := by rw [hq]; simp
  have hq_im : q.im = -(δ / 4) := by rw [hq]; simp
  have hquarter : |1 + δ / 4 - 1| = δ / 4 := by
    rw [show 1 + δ / 4 - 1 = δ / 4 by ring, abs_of_pos hpos]
  have hp_ball : p ∈ Metric.ball (1 : ℂ) δ := by
    refine mem_ball_one_of_re_im ?_
    rw [hp_re, hp_im, hquarter, abs_of_pos hpos]; linarith
  have hq_ball : q ∈ Metric.ball (1 : ℂ) δ := by
    refine mem_ball_one_of_re_im ?_
    rw [hq_re, hq_im, hquarter, abs_neg, abs_of_pos hpos]; linarith
  have hpA : p ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 1 < z.re} :=
    ⟨hp_ball, by show 1 < p.re; rw [hp_re]; linarith⟩
  have hpB : p ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im} :=
    ⟨hp_ball, by show 0 < p.im; rw [hp_im]; exact hpos⟩
  have hqAB : q ∈ (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 1 < z.re}) ∪
      (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im}) :=
    Or.inl ⟨hq_ball, by show 1 < q.re; rw [hq_re]; linarith⟩
  have hqC : q ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0} :=
    ⟨hq_ball, by show q.im < 0; rw [hq_im]; linarith⟩
  have hAB : IsPreconnected ((Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 1 < z.re}) ∪
      (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im})) :=
    IsPreconnected.union p hpA hpB hA hB
  have hABC : IsPreconnected (((Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 1 < z.re}) ∪
      (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im})) ∪
      (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0})) :=
    IsPreconnected.union q hqAB hqC hAB hC
  have hset : Metric.ball (1 : ℂ) δ ∩ Om1 =
      ((Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 1 < z.re}) ∪
        (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im})) ∪
        (Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0}) := by
    ext z
    simp only [Om1, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hb, him | hre⟩
      · rcases lt_or_gt_of_ne him with h | h
        · exact Or.inr ⟨hb, h⟩
        · exact Or.inl (Or.inr ⟨hb, h⟩)
      · exact Or.inl (Or.inl ⟨hb, hre⟩)
    · rintro ((⟨hb, hre⟩ | ⟨hb, hi⟩) | ⟨hb, hi⟩)
      · exact ⟨hb, Or.inr hre⟩
      · exact ⟨hb, Or.inl (ne_of_gt hi)⟩
      · exact ⟨hb, Or.inl (ne_of_lt hi)⟩
  rw [hset]
  exact hABC

theorem eqOn_zero_of_Om1ball_of_Ioo {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (1:ℂ) δ ∩ Work.A14D.Om1))
    (h : ∀ t : ℝ, t ∈ Set.Ioo 1 (1 + ε) → f (t : ℂ) = 0) :
    ∀ z ∈ Metric.ball (1:ℂ) δ ∩ Work.A14D.Om1, f z = 0 := by
  have hDopen : IsOpen (Metric.ball (1 : ℂ) δ ∩ Om1) := Metric.isOpen_ball.inter isOpen_Om1
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball (1 : ℂ) δ ∩ Om1) :=
    (Complex.analyticOnNhd_iff_differentiableOn hDopen).2 hf
  have hpre : IsPreconnected (Metric.ball (1 : ℂ) δ ∩ Om1) := isPreconnected_ball_inter_Om1 hδ
  -- the interior point `c = 1 + ε/2` of the interval, at which the zeros accumulate
  set c : ℂ := ((1 + ε / 2 : ℝ) : ℂ) with hc
  have hc_mem : c ∈ Metric.ball (1 : ℂ) δ ∩ Om1 := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : c - 1 = ((ε / 2 : ℝ) : ℂ) := by rw [hc]; push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
      linarith
    · right
      rw [hc]
      simp only [Complex.ofReal_re]
      linarith
  have hclos : c ∈ closure ({z | f z = 0} \ {c}) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    set s : ℝ := min η (ε / 2) / 2 with hsdef
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    have hs_pos : 0 < s := by
      rw [hsdef]; exact div_pos (lt_min hη hε2) (by norm_num)
    have hs_η : s < η := by
      rw [hsdef]; linarith [lt_min hη hε2, min_le_left η (ε / 2)]
    have hs_ε : s < ε / 2 := by
      rw [hsdef]; linarith [lt_min hη hε2, min_le_right η (ε / 2)]
    refine ⟨(((1 + ε / 2 - s : ℝ)) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · -- it is a zero of `f`
      refine h (1 + ε / 2 - s) ⟨?_, ?_⟩ <;> linarith
    · -- and it is distinct from `c`
      intro hcontra
      have hval : (1 + ε / 2 - s : ℝ) = 1 + ε / 2 := Complex.ofReal_inj.mp hcontra
      linarith
    · -- and it is within `η` of `c`
      have hsub : c - (((1 + ε / 2 - s : ℝ)) : ℂ) = ((s : ℝ) : ℂ) := by
        rw [hc]; push_cast; ring
      rw [Complex.dist_eq, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
      exact hs_η
  intro z hz
  exact hf_an.eqOn_zero_of_preconnected_of_mem_closure hpre hc_mem hclos hz

end Work.A14D
