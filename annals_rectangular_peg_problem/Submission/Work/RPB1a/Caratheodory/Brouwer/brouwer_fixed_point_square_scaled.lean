import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.brouwer_fixed_point_square

/-!
# Brouwer's fixed point theorem for a closed square, rescaled and translated

`Work.RPB1a.Caratheodory.Brouwer.brouwer_fixed_point_square_scaled`: every continuous map `F` of
the square `{y : ℝ × ℝ | max |y.1 - p.1| |y.2 - p.2| ≤ R}` (centre `p`, "radius" `R > 0` in the
max-norm) into itself has a fixed point.

The square and its rescaled version are related by the affine bijection

  `sqScale p R z = (p.1 + R * z.1, p.2 + R * z.2)`,

which maps the unit square `[-1,1] × [-1,1]` onto `{y | max |y.1 - p.1| |y.2 - p.2| ≤ R}`, with
inverse `sqUnscale p R z = ((z.1 - p.1)/R, (z.2 - p.2)/R)`.  Conjugating `F` by this bijection
turns the rescaled statement into the unit square statement
`brouwer_fixed_point_square`.
-/

namespace Work.RPB1a.Caratheodory.Brouwer

/-- The affine bijection `z ↦ (p.1 + R * z.1, p.2 + R * z.2)` of `ℝ × ℝ`, mapping the unit square
`[-1,1] × [-1,1]` onto the square `{y | max |y.1 - p.1| |y.2 - p.2| ≤ R}`. -/
private noncomputable def sqScale (p : ℝ × ℝ) (R : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + R * z.1, p.2 + R * z.2)

/-- The inverse `z ↦ ((z.1 - p.1)/R, (z.2 - p.2)/R)` of `sqScale p R` (for `R ≠ 0`). -/
private noncomputable def sqUnscale (p : ℝ × ℝ) (R : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 - p.1) / R, (z.2 - p.2) / R)

private lemma continuous_sqScale (p : ℝ × ℝ) (R : ℝ) : Continuous (sqScale p R) := by
  unfold sqScale; fun_prop

private lemma continuous_sqUnscale (p : ℝ × ℝ) (R : ℝ) : Continuous (sqUnscale p R) := by
  unfold sqUnscale; fun_prop

private lemma sqScale_sqUnscale (p : ℝ × ℝ) {R : ℝ} (hR : R ≠ 0) (z : ℝ × ℝ) :
    sqScale p R (sqUnscale p R z) = z := by
  unfold sqScale sqUnscale
  ext
  · rw [mul_div_cancel₀ (z.1 - p.1) hR]; ring
  · rw [mul_div_cancel₀ (z.2 - p.2) hR]; ring

private lemma sqUnscale_sqScale (p : ℝ × ℝ) {R : ℝ} (hR : R ≠ 0) (z : ℝ × ℝ) :
    sqUnscale p R (sqScale p R z) = z := by
  unfold sqScale sqUnscale
  ext
  · rw [show p.1 + R * z.1 - p.1 = R * z.1 by ring, mul_div_cancel_left₀ _ hR]
  · rw [show p.2 + R * z.2 - p.2 = R * z.2 by ring, mul_div_cancel_left₀ _ hR]

private lemma mul_le_self_iff {R a : ℝ} (hR : 0 < R) : R * a ≤ R ↔ a ≤ 1 := by
  have h : (R * a ≤ R * 1) ↔ (a ≤ 1) := mul_le_mul_iff_right₀ hR
  simpa using h

/-- `sqScale p R` carries the unit square onto the square of radius `R` about `p`. -/
private lemma sqScale_mem_iff (p : ℝ × ℝ) {R : ℝ} (hR : 0 < R) (z : ℝ × ℝ) :
    max |z.1| |z.2| ≤ 1 ↔
      max |(sqScale p R z).1 - p.1| |(sqScale p R z).2 - p.2| ≤ R := by
  have h1 : (sqScale p R z).1 - p.1 = R * z.1 := by simp [sqScale]
  have h2 : (sqScale p R z).2 - p.2 = R * z.2 := by simp [sqScale]
  rw [h1, h2, abs_mul, abs_mul, abs_of_pos hR, max_le_iff, max_le_iff]
  simp only [mul_le_self_iff hR]

/-- `sqUnscale p R` carries the square of radius `R` about `p` onto the unit square. -/
private lemma sqUnscale_mem_iff (p : ℝ × ℝ) {R : ℝ} (hR : 0 < R) (z : ℝ × ℝ) :
    max |(sqUnscale p R z).1| |(sqUnscale p R z).2| ≤ 1 ↔
      max |z.1 - p.1| |z.2 - p.2| ≤ R := by
  have h1 : (sqUnscale p R z).1 = (z.1 - p.1) / R := by simp [sqUnscale]
  have h2 : (sqUnscale p R z).2 = (z.2 - p.2) / R := by simp [sqUnscale]
  rw [h1, h2, max_le_iff, max_le_iff, abs_div, abs_div, abs_of_pos hR]
  simp only [div_le_one hR]

theorem brouwer_fixed_point_square_scaled (p : ℝ × ℝ) {R : ℝ} (hR : 0 < R)
    (F : (ℝ × ℝ) → (ℝ × ℝ)) (hF : Continuous F)
    (hmaps : ∀ y, max |y.1 - p.1| |y.2 - p.2| ≤ R →
      max |(F y).1 - p.1| |(F y).2 - p.2| ≤ R) :
    ∃ y, max |y.1 - p.1| |y.2 - p.2| ≤ R ∧ F y = y := by
  have hRne : R ≠ 0 := ne_of_gt hR
  -- Conjugate `F` by the affine bijection, obtaining a self-map `f` of the unit square.
  set f : ℝ × ℝ → ℝ × ℝ := fun z => sqUnscale p R (F (sqScale p R z)) with hf
  have hfc : Continuous f := by
    rw [hf]
    exact (continuous_sqUnscale p R).comp (hF.comp (continuous_sqScale p R))
  have hfmaps : ∀ z ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1,
      f z ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hz
    have hzmax : max |z.1| |z.2| ≤ 1 := max_le (abs_le.mpr hz.1) (abs_le.mpr hz.2)
    have h1 : max |(sqScale p R z).1 - p.1| |(sqScale p R z).2 - p.2| ≤ R :=
      (sqScale_mem_iff p hR z).mp hzmax
    have h2 := hmaps (sqScale p R z) h1
    have h3 : max |(sqUnscale p R (F (sqScale p R z))).1|
        |(sqUnscale p R (F (sqScale p R z))).2| ≤ 1 :=
      (sqUnscale_mem_iff p hR (F (sqScale p R z))).mpr h2
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    exact ⟨abs_le.mp (le_trans (le_max_left _ _) h3),
           abs_le.mp (le_trans (le_max_right _ _) h3)⟩
  obtain ⟨x, hxmem, hxfix⟩ := brouwer_fixed_point_square f hfc hfmaps
  -- The corresponding point of the rescaled square is a fixed point of `F`.
  have hxmem' : max |x.1| |x.2| ≤ 1 := by
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hxmem
    exact max_le (abs_le.mpr hxmem.1) (abs_le.mpr hxmem.2)
  refine ⟨sqScale p R x, (sqScale_mem_iff p hR x).mp hxmem', ?_⟩
  have h : sqUnscale p R (F (sqScale p R x)) = x := by
    have hh := hxfix
    rw [hf] at hh
    simpa using hh
  have h' := congrArg (sqScale p R) h
  rwa [sqScale_sqUnscale p hRne] at h'

end Work.RPB1a.Caratheodory.Brouwer
