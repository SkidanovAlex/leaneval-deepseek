import Mathlib

namespace Work.C17b

open Set

/-- Membership helper: if `|z.re| + |z.im| < δ` then `z` lies in the open disc of
radius `δ`.  We bound `‖z‖ ≤ |z.re| + |z.im|`. -/
private lemma mem_ball_of_re_im_le {δ : ℝ} {z : ℂ} (h : |z.re| + |z.im| < δ) :
    z ∈ Metric.ball (0 : ℂ) δ := by
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im z) h

/-- The open disc of radius `δ` slit along the closed non-negative real axis,
i.e. `{u : ℂ | ‖u‖ < δ}` with the ray `[0, δ)` removed, is preconnected.

Indeed it is the union of the three convex (hence preconnected) pieces where
`re u < 0`, `0 < im u`, resp. `im u < 0`; the first piece meets each of the
other two, so the union is preconnected. -/
theorem isPreconnected_slitBall {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0 ∨ u.im ≠ 0}) := by
  have hpos : (0 : ℝ) < δ / 4 := by linarith
  -- the three convex pieces
  have hA : IsPreconnected (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0}) :=
    ((convex_ball (0 : ℂ) δ).inter ((convex_Iio (0 : ℝ)).linear_preimage Complex.reLm)).isPreconnected
  have hB : IsPreconnected (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | 0 < u.im}) :=
    ((convex_ball (0 : ℂ) δ).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)).isPreconnected
  have hC : IsPreconnected (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.im < 0}) :=
    ((convex_ball (0 : ℂ) δ).inter ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm)).isPreconnected
  -- two witness points in the left half-plane, one above and one below the axis
  set p : ℂ := -(δ / 4) + (δ / 4 : ℂ) * Complex.I with hpdef
  set q : ℂ := -(δ / 4) - (δ / 4 : ℂ) * Complex.I with hqdef
  have hp_re : p.re = -(δ / 4) := by simp [hpdef]
  have hp_im : p.im = δ / 4 := by simp [hpdef]
  have hq_re : q.re = -(δ / 4) := by simp [hqdef]
  have hq_im : q.im = -(δ / 4) := by simp [hqdef]
  have hp_ball : p ∈ Metric.ball (0 : ℂ) δ := by
    refine mem_ball_of_re_im_le ?_
    rw [hp_re, hp_im]
    simp only [abs_neg, abs_of_pos hpos]
    linarith
  have hq_ball : q ∈ Metric.ball (0 : ℂ) δ := by
    refine mem_ball_of_re_im_le ?_
    rw [hq_re, hq_im]
    simp only [abs_neg, abs_of_pos hpos]
    linarith
  have hp_re' : p.re < 0 := by rw [hp_re]; linarith
  have hp_im' : 0 < p.im := by rw [hp_im]; linarith
  have hq_re' : q.re < 0 := by rw [hq_re]; linarith
  have hq_im' : q.im < 0 := by rw [hq_im]; linarith
  -- glue: (A ∪ B) is preconnected, and meets C in q
  have hAB : IsPreconnected ((Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0}) ∪
      (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | 0 < u.im})) :=
    IsPreconnected.union p ⟨hp_ball, hp_re'⟩ ⟨hp_ball, hp_im'⟩ hA hB
  have hABC : IsPreconnected (((Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0}) ∪
      (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | 0 < u.im})) ∪
      (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.im < 0})) :=
    IsPreconnected.union q (Or.inl ⟨hq_ball, hq_re'⟩) ⟨hq_ball, hq_im'⟩ hAB hC
  -- identify the union with the slit ball
  have hset : Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0 ∨ u.im ≠ 0}
      = ((Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0}) ∪
        (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | 0 < u.im})) ∪
        (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.im < 0}) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hb, hr | hi⟩
      · exact Or.inl (Or.inl ⟨hb, hr⟩)
      · rcases lt_or_gt_of_ne hi with h | h
        · exact Or.inr ⟨hb, h⟩
        · exact Or.inl (Or.inr ⟨hb, h⟩)
    · rintro ((⟨hb, hr⟩ | ⟨hb, hi⟩) | ⟨hb, hi⟩)
      · exact ⟨hb, Or.inl hr⟩
      · exact ⟨hb, Or.inr (ne_of_gt hi)⟩
      · exact ⟨hb, Or.inr (ne_of_lt hi)⟩
  rw [hset]
  exact hABC

end Work.C17b
