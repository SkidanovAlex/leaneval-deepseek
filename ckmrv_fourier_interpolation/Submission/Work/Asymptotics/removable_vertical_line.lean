/-
# Removing a vertical line for holomorphy

A continuous function on an open set `U ⊆ ℍ` which is complex differentiable off a vertical line
`Re z = x` is complex differentiable on all of `U`.

The proof is Morera's theorem in the form of Mathlib's Cauchy–Goursat theorem for rectangles
(`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`, whose conclusion is
the vanishing of the oriented rectangle integral).  Every rectangle contained in `U` is cut by the
line `Re z = x` into two closed half-rectangles, each of whose *interiors* avoids the line; the
integral over the boundary of the big rectangle is the sum of the integrals over the two halves,
and each half vanishes by Cauchy–Goursat.  (This is why an ordinary rectangle theorem suffices and
no limiting argument is needed: one splits first, then applies the theorem.)  Vanishing of the
rectangle integrals is exactly `Complex.IsConservativeOn`, and Mathlib's Morera theorem for disks
`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn` finishes the job.

The complex-plane statement is proved first and then transferred to `ℍ` through the chart
`UpperHalfPlane.ofComplex` (Mathlib's `UpperHalfPlane.mdifferentiableAt_iff`).
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD

open Complex MeasureTheory Filter Topology Set
open scoped Real Manifold UpperHalfPlane

namespace Work.Asymptotics

noncomputable section

set_option linter.unusedSimpArgs false

/-! ## 1. The rectangle integral and its symmetries -/

/-- The oriented rectangle integral of `f` over the rectangle with corners `z` and `w`, written in
the normal form used by Mathlib's Cauchy–Goursat theorem for rectangles. -/
def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (((∫ t : ℝ in z.re..w.re, f (t + z.im * Complex.I)) -
      ∫ t : ℝ in z.re..w.re, f (t + w.im * Complex.I)) +
    Complex.I • ∫ t : ℝ in z.im..w.im, f (w.re + t * Complex.I)) -
  Complex.I • ∫ t : ℝ in z.im..w.im, f (z.re + t * Complex.I)

/-- Coordinates of a point of the form `t + c·I`. -/
lemma add_ofReal_mul_I_re (t c : ℝ) : ((t : ℂ) + (c : ℂ) * Complex.I).re = t := by simp

/-- Coordinates of a point of the form `t + c·I`. -/
lemma add_ofReal_mul_I_im (t c : ℝ) : ((t : ℂ) + (c : ℂ) * Complex.I).im = c := by simp

/-- Membership in a `uIcc` from the two inequalities, assuming the endpoints are ordered. -/
lemma mem_uIcc_of_le' {a b c : ℝ} (hab : a ≤ b) (hac : a ≤ c) (hcb : c ≤ b) : c ∈ uIcc a b := by
  rw [uIcc_of_le hab]; exact ⟨hac, hcb⟩

/-- Membership in a `uIcc` from membership in the interval with endpoints `min` and `max`. -/
lemma mem_uIcc_of_mem_Ioo_minmax {a b c : ℝ} (h : c ∈ Ioo (min a b) (max a b)) : c ∈ uIcc a b := by
  simp only [mem_uIcc]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at h; exact Or.inl ⟨h.1.le, h.2.le⟩
  · rw [min_eq_right hab, max_eq_left hab] at h; exact Or.inr ⟨h.1.le, h.2.le⟩

/-- The *closed* rectangle of `Complex.Rectangle` contains the rectangle with the same corners but
described through `min` and `max` (which is the shape in which Mathlib states differentiability
hypotheses for rectangle integrals). -/
lemma mem_rect_of_mem_openRect {z w u : ℂ}
    (hu : u ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)) :
    u ∈ Rectangle z w := by
  simp only [Complex.Rectangle, mem_reProdIm] at hu ⊢
  exact ⟨mem_uIcc_of_mem_Ioo_minmax hu.1, mem_uIcc_of_mem_Ioo_minmax hu.2⟩

/-- `rectInt` is the sum of the two wedge integrals: Mathlib's `wedgeIntegral_add_wedgeIntegral_eq`
with the orientation of the terms rearranged.  Thus `rectInt f z w = 0` is exactly
`Complex.IsConservativeOn` at the rectangle with corners `z, w`. -/
lemma rectInt_eq_wedge_add (f : ℂ → ℂ) (z w : ℂ) :
    rectInt f z w = wedgeIntegral z w f + wedgeIntegral w z f := by
  rw [rectInt, wedgeIntegral_add_wedgeIntegral_eq]

/-- `rectInt` is symmetric in its two rectangle corners. -/
lemma rectInt_comm (f : ℂ → ℂ) (z w : ℂ) : rectInt f z w = rectInt f w z := by
  rw [rectInt_eq_wedge_add, rectInt_eq_wedge_add, add_comm]

/-- `Rectangle` is symmetric in its two corners. -/
lemma Rectangle_comm (z w : ℂ) : Rectangle z w = Rectangle w z := by
  simp only [Complex.Rectangle, uIcc_comm]

/-- Swapping the imaginary parts of the two corners does not change their rectangle. -/
lemma Rectangle_swap (z w : ℂ) :
    Rectangle (z.re + w.im * Complex.I) (w.re + z.im * Complex.I) = Rectangle z w := by
  simp only [Complex.Rectangle, add_ofReal_mul_I_re, add_ofReal_mul_I_im, uIcc_comm]

/-- Swapping the imaginary parts of the two corners changes the sign of the rectangle integral. -/
lemma rectInt_swap (f : ℂ → ℂ) (z w : ℂ) :
    rectInt f (z.re + w.im * Complex.I) (w.re + z.im * Complex.I) = -rectInt f z w := by
  unfold rectInt
  simp only [add_ofReal_mul_I_re, add_ofReal_mul_I_im]
  rw [intervalIntegral.integral_symm w.im z.im, intervalIntegral.integral_symm w.im z.im,
    intervalIntegral.integral_symm w.re z.re, intervalIntegral.integral_symm w.re z.re]
  ring

/-! ## 2. The rectangle integral vanishes off the line -/

/-- **Cauchy–Goursat when the (open) rectangle avoids the line.**  If the rectangle integral over
the rectangle with corners `z, w` can be evaluated by the rectangle Cauchy theorem, i.e. if no point
of the open rectangle with corners `z, w` lies on `Re z = x`, then it vanishes. -/
lemma rectInt_eq_zero_of_avoid {f : ℂ → ℂ} {U : Set ℂ} {x : ℝ} (hcont : ContinuousOn f U)
    (hdiff : DifferentiableOn ℂ f (U \ {z | z.re = x}))
    (z w : ℂ) (hzw : Rectangle z w ⊆ U)
    (hav : ∀ u ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      u.re ≠ x) :
    rectInt f z w = 0 := by
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w (hcont.mono hzw) ?_
  refine hdiff.mono fun u hu => ⟨hzw (mem_rect_of_mem_openRect hu), ?_⟩
  simpa using hav u hu

/-- Interval integrability of `t ↦ f (t + c·I)` over a subinterval of `[z.re, w.re]`, when `f` is
continuous on the rectangle with corners `z, w` and `c` lies between the imaginary parts. -/
lemma rectIntegrable {f : ℂ → ℂ} {U : Set ℂ} (hcont : ContinuousOn f U) {z w : ℂ}
    (hzw : Rectangle z w ⊆ U) {c : ℝ} (hc : z.im ≤ c ∧ c ≤ w.im) {a b : ℝ} (ha : z.re ≤ a)
    (hab : a ≤ b) (hb : b ≤ w.re) :
    IntervalIntegrable (fun t : ℝ => f (t + c * Complex.I)) volume a b := by
  refine ((hcont.mono hzw).comp (by fun_prop) ?_).intervalIntegrable
  intro t ht
  rw [Complex.Rectangle, mem_reProdIm, add_ofReal_mul_I_re, add_ofReal_mul_I_im]
  refine ⟨?_, ?_⟩
  · rw [uIcc_of_le hab] at ht
    exact Icc_subset_uIcc ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  · exact Icc_subset_uIcc ⟨hc.1, hc.2⟩

/-- **Splitting a rectangle along a vertical line.**  The rectangle integral over a rectangle is the
sum of the rectangle integrals over the two halves, when `z.re ≤ x ≤ w.re` (and the imaginary parts
are ordered so that the vertical sides of the two halves match up). -/
lemma rectInt_split {f : ℂ → ℂ} {U : Set ℂ} (hcont : ContinuousOn f U) {z w : ℂ}
    (hzw : Rectangle z w ⊆ U) (_hre : z.re ≤ w.re) (him : z.im ≤ w.im) {x : ℝ}
    (h₁ : z.re ≤ x) (h₂ : x ≤ w.re) :
    rectInt f z w = rectInt f z (x + w.im * Complex.I) + rectInt f (x + z.im * Complex.I) w := by
  have hi₁ : IntervalIntegrable (fun t : ℝ => f (t + z.im * Complex.I)) volume z.re x :=
    rectIntegrable hcont hzw ⟨le_rfl, him⟩ le_rfl h₁ h₂
  have hi₂ : IntervalIntegrable (fun t : ℝ => f (t + z.im * Complex.I)) volume x w.re :=
    rectIntegrable hcont hzw ⟨le_rfl, him⟩ h₁ h₂ le_rfl
  have hi₃ : IntervalIntegrable (fun t : ℝ => f (t + w.im * Complex.I)) volume z.re x :=
    rectIntegrable hcont hzw ⟨him, le_rfl⟩ le_rfl h₁ h₂
  have hi₄ : IntervalIntegrable (fun t : ℝ => f (t + w.im * Complex.I)) volume x w.re :=
    rectIntegrable hcont hzw ⟨him, le_rfl⟩ h₁ h₂ le_rfl
  unfold rectInt
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add, sub_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,
    ← intervalIntegral.integral_add_adjacent_intervals hi₃ hi₄]
  ring

/-- **Vanishing of the rectangle integral, for rectangles whose corners are ordered coordinatewise.**
The line cuts such a rectangle into an empty piece and the whole rectangle, or into a left and a
right half; in the latter case both halves are handled by `rectInt_eq_zero_of_avoid`, since their
*open* rectangles avoid the line. -/
lemma rectInt_eq_zero_of_sorted {f : ℂ → ℂ} {U : Set ℂ} {x : ℝ} (hcont : ContinuousOn f U)
    (hdiff : DifferentiableOn ℂ f (U \ {z | z.re = x}))
    (z w : ℂ) (hzw : Rectangle z w ⊆ U) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    rectInt f z w = 0 := by
  by_cases h₁ : x ≤ z.re
  · refine rectInt_eq_zero_of_avoid hcont hdiff z w hzw fun u hu => ?_
    rw [mem_reProdIm, min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hu
    exact ne_of_gt (lt_of_le_of_lt h₁ hu.1.1)
  · by_cases h₂ : w.re ≤ x
    · refine rectInt_eq_zero_of_avoid hcont hdiff z w hzw fun u hu => ?_
      rw [mem_reProdIm, min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hu
      exact ne_of_lt (lt_of_lt_of_le hu.1.2 h₂)
    · have h₁' : z.re < x := lt_of_not_ge h₁
      have h₂' : x < w.re := lt_of_not_ge h₂
      rw [rectInt_split hcont hzw hre him h₁'.le h₂'.le]
      have hleft : rectInt f z (x + w.im * Complex.I) = 0 := by
        refine rectInt_eq_zero_of_avoid hcont hdiff z (x + w.im * Complex.I) ?_ fun u hu => ?_
        · intro v hv
          apply hzw
          simp only [Complex.Rectangle, add_ofReal_mul_I_re x w.im,
            add_ofReal_mul_I_im x w.im, mem_reProdIm] at hv ⊢
          rw [uIcc_of_le h₁'.le, uIcc_of_le him] at hv
          exact ⟨mem_uIcc_of_le' hre hv.1.1 (le_trans hv.1.2 h₂'.le),
            mem_uIcc_of_le' him hv.2.1 hv.2.2⟩
        · rw [mem_reProdIm, add_ofReal_mul_I_re x w.im, add_ofReal_mul_I_im x w.im,
            min_eq_left h₁'.le, max_eq_right h₁'.le, min_eq_left him, max_eq_right him] at hu
          exact ne_of_lt hu.1.2
      have hright : rectInt f (x + z.im * Complex.I) w = 0 := by
        refine rectInt_eq_zero_of_avoid hcont hdiff (x + z.im * Complex.I) w ?_ fun u hu => ?_
        · intro v hv
          apply hzw
          simp only [Complex.Rectangle, add_ofReal_mul_I_re x z.im,
            add_ofReal_mul_I_im x z.im, mem_reProdIm] at hv ⊢
          rw [uIcc_of_le h₂'.le, uIcc_of_le him] at hv
          exact ⟨mem_uIcc_of_le' hre (le_of_lt (lt_of_lt_of_le h₁' hv.1.1)) hv.1.2,
            mem_uIcc_of_le' him hv.2.1 hv.2.2⟩
        · rw [mem_reProdIm, add_ofReal_mul_I_re x z.im, add_ofReal_mul_I_im x z.im,
            min_eq_left h₂'.le, max_eq_right h₂'.le, min_eq_left him, max_eq_right him] at hu
          exact ne_of_gt hu.1.1
      rw [hleft, hright, add_zero]

/-- **Vanishing of the rectangle integral for an arbitrary rectangle.**  The two symmetries
`rectInt_comm` (free) and `rectInt_swap` (sign change) put the corners in coordinatewise order. -/
lemma rectInt_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {x : ℝ} (hcont : ContinuousOn f U)
    (hdiff : DifferentiableOn ℂ f (U \ {z | z.re = x})) (z w : ℂ) (hzw : Rectangle z w ⊆ U) :
    rectInt f z w = 0 := by
  rcases le_or_gt z.re w.re with hre | hre
  · rcases le_or_gt z.im w.im with him | him
    · exact rectInt_eq_zero_of_sorted hcont hdiff z w hzw hre him
    · rw [← neg_eq_zero, ← rectInt_swap]
      refine rectInt_eq_zero_of_sorted hcont hdiff _ _ ?_ ?_ ?_
      · rwa [Rectangle_swap]
      · simp only [add_ofReal_mul_I_re, add_ofReal_mul_I_im]; exact hre
      · simp only [add_ofReal_mul_I_re, add_ofReal_mul_I_im]; exact him.le
  · rw [rectInt_comm]
    rcases le_or_gt w.im z.im with him | him
    · exact rectInt_eq_zero_of_sorted hcont hdiff w z (by rwa [Rectangle_comm]) hre.le him
    · rw [← neg_eq_zero, ← rectInt_swap]
      refine rectInt_eq_zero_of_sorted hcont hdiff _ _ ?_ ?_ ?_
      · rwa [Rectangle_swap, Rectangle_comm]
      · simp only [add_ofReal_mul_I_re, add_ofReal_mul_I_im]; exact hre.le
      · simp only [add_ofReal_mul_I_re, add_ofReal_mul_I_im]; exact him.le

/-- **Removal of a vertical line, on `ℂ`.**  A continuous function on an open set `U ⊆ ℂ` which is
complex differentiable off the vertical line `Re z = x` is complex differentiable on `U`. -/
theorem differentiableOn_of_differentiableOn_compl_vertical {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (x : ℝ) (hcont : ContinuousOn f U)
    (hdiff : DifferentiableOn ℂ f (U \ {z | z.re = x})) : DifferentiableOn ℂ f U :=
  (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
    ⟨fun z w hzw => by
      have h0 : wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
        rw [← rectInt_eq_wedge_add]
        exact rectInt_eq_zero hcont hdiff z w hzw
      exact eq_neg_of_add_eq_zero_left h0, hcont⟩

/-! ## 3. Transfer to the upper half plane -/

/-- The source of the chart `UpperHalfPlane.ofComplex` is the upper half plane. -/
lemma ofComplex_source_eq :
    UpperHalfPlane.ofComplex.source = {z : ℂ | 0 < z.im} := by
  rw [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]

/-- **Removal of a vertical line for holomorphy.** If `f : ℍ → ℂ` is continuous on an open set
`U` and complex differentiable on `U` minus the vertical line `Re z = x`, then `f` is complex
differentiable on all of `U`.  (Morera: triangles crossing the line are split into two halves,
each of which is a limit of polygons contained in one of the two half-planes.) -/
theorem removable_vertical_line {f : UpperHalfPlane → ℂ}
    {U : Set UpperHalfPlane} (hU : IsOpen U) (x : ℝ)
    (hcont : ContinuousOn f U)
    (hdiff : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f
      (U \ {z : UpperHalfPlane | z.re = x})) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f U := by
  -- an open set of `ℂ` cutting out `U`
  obtain ⟨W, hWopen, hWU⟩ := (UpperHalfPlane.isOpenEmbedding_coe.isInducing.isOpen_iff).mp hU
  -- the open set of `ℂ` on which the plane statement is applied
  set V : Set ℂ := W ∩ {z : ℂ | 0 < z.im} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact hWopen.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hcont' : ContinuousOn (f ∘ UpperHalfPlane.ofComplex) V := by
    refine hcont.comp (UpperHalfPlane.ofComplex.continuousOn.mono ?_) ?_
    · intro z hz
      simp only [hVdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
      rw [ofComplex_source_eq]
      exact hz.2
    · intro z hz
      simp only [hVdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
      rw [← hWU, UpperHalfPlane.ofComplex_apply_of_im_pos hz.2]
      exact hz.1
  have hdiff' : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex)
      (V \ {z : ℂ | z.re = x}) := by
    intro z hz
    rw [Set.mem_sdiff] at hz
    obtain ⟨hzV, hzL⟩ := hz
    simp only [hVdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hzV
    obtain ⟨hzW, hzim⟩ := hzV
    have hzre : z.re ≠ x := by simpa using hzL
    have hzU : (⟨z, hzim⟩ : UpperHalfPlane) ∈ U := by
      rw [← hWU]
      exact hzW
    have hopen : IsOpen (U \ {w : UpperHalfPlane | w.re = x}) := by
      rw [Set.sdiff_eq]
      exact hU.inter (isClosed_eq UpperHalfPlane.continuous_re continuous_const).isOpen_compl
    have hmem : (⟨z, hzim⟩ : UpperHalfPlane) ∈ U \ {w : UpperHalfPlane | w.re = x} :=
      ⟨hzU, by simpa using hzre⟩
    have hAt : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f
        (⟨z, hzim⟩ : UpperHalfPlane) :=
      (hdiff _ hmem).mdifferentiableAt (hopen.mem_nhds hmem)
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp hAt).differentiableWithinAt
  have hD : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) V :=
    differentiableOn_of_differentiableOn_compl_vertical hVopen x hcont' hdiff'
  intro τ hτ
  have hτV : (τ : ℂ) ∈ V := by
    rw [hVdef]
    refine ⟨?_, τ.im_pos⟩
    have h : τ ∈ UpperHalfPlane.coe ⁻¹' W := by rw [hWU]; exact hτ
    exact h
  have hAt : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (τ : ℂ) :=
    hD.differentiableAt (hVopen.mem_nhds hτV)
  exact (UpperHalfPlane.mdifferentiableAt_iff.mpr hAt).mdifferentiableWithinAt

end

end Work.Asymptotics
