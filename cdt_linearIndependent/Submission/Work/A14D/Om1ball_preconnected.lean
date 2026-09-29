import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C17b.isPreconnected_slitBall

/-!
# `Work.A14D.Om1ball_preconnected`

The set `Om1 = {z : ℂ | z.im ≠ 0 ∨ 1 < z.re}` is the slit plane `ℂ ∖ (−∞, 1]`.  We show that
its intersection with any open disc `ball 1 ρ` (`ρ > 0`) is preconnected: the disc with the
radial slit `[1−ρ, 1]` removed.

The proof decomposes the set into three convex (hence preconnected) pieces,
`ball 1 ρ ∩ {im > 0}`, `ball 1 ρ ∩ {1 < re}` and `ball 1 ρ ∩ {im < 0}`, glued at two explicit
points `1 + ρ/4 ± (ρ/4) I`.
-/

open Set Metric Complex

noncomputable section

namespace Work.A14D

/-- Point above the slit, in the upper half of the disc `ball 1 ρ`. -/
private def pPt (ρ : ℝ) : ℂ := 1 + ((ρ / 4 : ℝ) : ℂ) + ((ρ / 4 : ℝ) : ℂ) * Complex.I

/-- Point below the slit, in the lower half of the disc `ball 1 ρ`. -/
private def qPt (ρ : ℝ) : ℂ := 1 + ((ρ / 4 : ℝ) : ℂ) - ((ρ / 4 : ℝ) : ℂ) * Complex.I

theorem Om1ball_preconnected {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (Metric.ball (1 : ℂ) ρ ∩ Om1) := by
  have h4 : (0 : ℝ) < ρ / 4 := by linarith
  -- the three convex pieces
  have hA : IsPreconnected (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) :=
    ((convex_ball (1 : ℂ) ρ).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)).isPreconnected
  have hB : IsPreconnected (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | z.im < 0}) :=
    ((convex_ball (1 : ℂ) ρ).inter ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm)).isPreconnected
  have hC : IsPreconnected (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 1 < z.re}) :=
    ((convex_ball (1 : ℂ) ρ).inter ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reLm)).isPreconnected
  -- the two witnesses
  have hp_re : (pPt ρ).re = 1 + ρ / 4 := by
    simp [pPt, Complex.add_re, Complex.mul_re]
  have hp_im : (pPt ρ).im = ρ / 4 := by
    simp [pPt, Complex.add_im, Complex.mul_im]
  have hq_re : (qPt ρ).re = 1 + ρ / 4 := by
    simp [qPt, Complex.add_re, Complex.sub_re, Complex.mul_re]
  have hq_im : (qPt ρ).im = -(ρ / 4) := by
    simp [qPt, Complex.add_im, Complex.sub_im, Complex.mul_im]
  have hp_ball : pPt ρ ∈ Metric.ball (1 : ℂ) ρ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h : pPt ρ - 1 = ((ρ / 4 : ℝ) : ℂ) + ((ρ / 4 : ℝ) : ℂ) * Complex.I := by
      simp only [pPt]; ring
    rw [h]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, sub_zero,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one, add_zero]
    rw [zero_add, abs_of_pos h4]
    linarith
  have hq_ball : qPt ρ ∈ Metric.ball (1 : ℂ) ρ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h : qPt ρ - 1 = ((ρ / 4 : ℝ) : ℂ) - ((ρ / 4 : ℝ) : ℂ) * Complex.I := by
      simp only [qPt]; ring
    rw [h]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, sub_zero,
      Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one, zero_sub]
    rw [abs_neg, add_zero, abs_of_pos h4]
    linarith
  have hp_im' : 0 < (pPt ρ).im := by rw [hp_im]; linarith
  have hp_re' : 1 < (pPt ρ).re := by rw [hp_re]; linarith
  have hq_im' : (qPt ρ).im < 0 := by rw [hq_im]; linarith
  have hq_re' : 1 < (qPt ρ).re := by rw [hq_re]; linarith
  -- glue: (A ∪ C) preconnected, then glue B at q
  have hAC : IsPreconnected ((Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) ∪
      (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 1 < z.re})) :=
    IsPreconnected.union (pPt ρ) ⟨hp_ball, hp_im'⟩ ⟨hp_ball, hp_re'⟩ hA hC
  have hACB : IsPreconnected (((Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) ∪
      (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 1 < z.re})) ∪
      (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | z.im < 0})) :=
    IsPreconnected.union (qPt ρ) (Or.inr ⟨hq_ball, hq_re'⟩) ⟨hq_ball, hq_im'⟩ hAC hB
  -- identify the union with the target set
  have hset : Metric.ball (1 : ℂ) ρ ∩ Om1
      = ((Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) ∪
        (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | 1 < z.re})) ∪
        (Metric.ball (1 : ℂ) ρ ∩ {z : ℂ | z.im < 0}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, Om1]
    constructor
    · rintro ⟨hb, hi | hr⟩
      · rcases lt_or_gt_of_ne hi with h | h
        · exact Or.inr ⟨hb, h⟩
        · exact Or.inl (Or.inl ⟨hb, h⟩)
      · exact Or.inl (Or.inr ⟨hb, hr⟩)
    · rintro ((⟨hb, hi⟩ | ⟨hb, hr⟩) | ⟨hb, hi⟩)
      · exact ⟨hb, Or.inl (ne_of_gt hi)⟩
      · exact ⟨hb, Or.inr hr⟩
      · exact ⟨hb, Or.inl (ne_of_lt hi)⟩
  rw [hset]
  exact hACB

end Work.A14D

end
