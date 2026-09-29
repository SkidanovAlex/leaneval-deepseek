import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.om1_geometry

/-!
# A14D — the geometry of the crux of `crux_jump`

The set `cruxV = ball 1 (8/9) ∩ {Re < 1}` is the convex open set on which the local holomorphic
part `E1 = D − (π i c/4)·u_h·log (·−1)` of the jump `D` is continued across the real interval
`(1/9, 1)`.  It contains that interval but avoids all three singular points `0, 1/9, 1` of the
operator `LZ`, so the linear ODE is regular on it.

`cruxU = {Im > 0}` and `cruxL = {Im < 0}` are the two open half-planes; `cruxU ∩ cruxV` and
`cruxL ∩ cruxV` are the two half-discs on which `D` is compared with its continuation.
-/

namespace Work.A14D

open Complex Metric

noncomputable section

/-- The open disc `ball 1 (8/9)` cut by the half-plane `Re < 1`. -/
def cruxV : Set ℂ := Metric.ball (1 : ℂ) (8 / 9) ∩ {z : ℂ | z.re < 1}

/-- The open upper half-plane. -/
def cruxU : Set ℂ := {z : ℂ | 0 < z.im}

/-- The open lower half-plane. -/
def cruxL : Set ℂ := {z : ℂ | z.im < 0}

lemma isOpen_cruxV : IsOpen cruxV :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_re continuous_const)

lemma convex_cruxV : Convex ℝ cruxV :=
  (convex_ball (1 : ℂ) (8 / 9)).inter (convex_halfSpace_re_lt 1)

lemma isOpen_cruxU : IsOpen cruxU := isOpen_lt continuous_const Complex.continuous_im

lemma isOpen_cruxL : IsOpen cruxL := isOpen_lt Complex.continuous_im continuous_const

lemma convex_cruxU : Convex ℝ cruxU := convex_halfSpace_im_gt 0

lemma convex_cruxL : Convex ℝ cruxL := convex_halfSpace_im_lt 0

lemma mem_cruxV_iff {z : ℂ} : z ∈ cruxV ↔ ‖z - 1‖ < 8 / 9 ∧ z.re < 1 := by
  rw [cruxV, Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm, Set.mem_ofPred_eq]

/-- `PZ = z(1−z)(1−9z)` vanishes only at `0, 1, 1/9`, none of which lies in `cruxV`. -/
lemma PZ_ne_zero_of_mem_cruxV {z : ℂ} (hz : z ∈ cruxV) : PZ z ≠ 0 := by
  obtain ⟨hnorm, hre⟩ := mem_cruxV_iff.mp hz
  intro h
  rw [PZ] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [h2] at hnorm
      simp at hnorm
      exact absurd hnorm (by norm_num)
    · have hz1 : z = 1 := by linear_combination -h2
      rw [hz1] at hre
      simp at hre
  · have h3 : 9 * z = 1 := by linear_combination -h1
    have hz9 : z = 1 / 9 := by
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h3
    rw [hz9] at hnorm
    have h8 : ‖((1 : ℂ) / 9) - 1‖ = 8 / 9 := by
      have : ((1 : ℂ) / 9 - 1) = ((-(8 / 9) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real]
      norm_num
    rw [h8] at hnorm
    exact absurd hnorm (lt_irrefl _)

lemma cruxU_subset_Om1 : cruxU ⊆ Om1 := fun z hz => Or.inl (ne_of_gt hz)

lemma cruxL_subset_Om1 : cruxL ⊆ Om1 := fun z hz => Or.inl (ne_of_lt hz)

lemma cruxU_inter_cruxV_subset_Om1 : cruxU ∩ cruxV ⊆ Om1 :=
  fun z hz => cruxU_subset_Om1 hz.1

lemma cruxL_inter_cruxV_subset_Om1 : cruxL ∩ cruxV ⊆ Om1 :=
  fun z hz => cruxL_subset_Om1 hz.1

lemma PZ_ne_zero_of_mem_cruxU_inter {z : ℂ} (hz : z ∈ cruxU ∩ cruxV) : PZ z ≠ 0 :=
  PZ_ne_zero_of_im_pos hz.1

lemma PZ_ne_zero_of_mem_cruxL_inter {z : ℂ} (hz : z ∈ cruxL ∩ cruxV) : PZ z ≠ 0 :=
  PZ_ne_zero_of_im_neg hz.1

/-- Any real `x` with `1/9 < x < 1` lies in `cruxV`. -/
lemma ofReal_mem_cruxV {x : ℝ} (hx : x ∈ Set.Ioo (1 / 9) 1) : (x : ℂ) ∈ cruxV := by
  obtain ⟨h1, h2⟩ := hx
  rw [mem_cruxV_iff]
  constructor
  · have hsub : (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : x - 1 < 0)]
    linarith
  · simpa using h2

/-- For `δ ≤ 8/9` every real `x` with `1 - δ < x < 1` lies in `cruxV`. -/
lemma ofReal_mem_cruxV_of_near_one {δ x : ℝ} (hδ : δ ≤ 8 / 9) (hx : x ∈ Set.Ioo (1 - δ) 1) :
    (x : ℂ) ∈ cruxV := by
  refine ofReal_mem_cruxV ⟨?_, hx.2⟩
  linarith [hx.1, hδ]

/-- `cruxV ∩ Om1` is exactly the union of the two half-discs `cruxU ∩ cruxV`, `cruxL ∩ cruxV`. -/
lemma cruxV_inter_Om1_eq : cruxV ∩ Om1 = (cruxU ∩ cruxV) ∪ (cruxL ∩ cruxV) := by
  ext z
  constructor
  · rintro ⟨hzV, him | hre'⟩
    · obtain ⟨-, hre⟩ := mem_cruxV_iff.mp hzV
      rcases lt_or_gt_of_ne him with h | h
      · exact Or.inr ⟨h, hzV⟩
      · exact Or.inl ⟨h, hzV⟩
    · obtain ⟨-, hre⟩ := mem_cruxV_iff.mp hzV
      exact absurd hre' (not_lt.mpr hre.le)
  · rintro (⟨him, hzV⟩ | ⟨him, hzV⟩)
    · exact ⟨hzV, Or.inl (ne_of_gt him)⟩
    · exact ⟨hzV, Or.inl (ne_of_lt him)⟩

/-- The point `1/2 + i/10`, a witness that `cruxU ∩ cruxV` is nonempty. -/
theorem nonempty_cruxU_inter_cruxV : (cruxU ∩ cruxV).Nonempty := by
  refine ⟨((1 / 2 : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · show 0 < (((1 / 2 : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I).im
    simp
  · rw [mem_cruxV_iff]
    constructor
    · have hsub : ((1 / 2 : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I - 1
          = ((-(1 / 2) : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hsub]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, sub_zero,
        Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one, add_zero]
      norm_num
    · show (((1 / 2 : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I).re < 1
      simp
      norm_num

/-- The point `1/2 - i/10`, a witness that `cruxL ∩ cruxV` is nonempty. -/
theorem nonempty_cruxL_inter_cruxV : (cruxL ∩ cruxV).Nonempty := by
  refine ⟨((1 / 2 : ℝ) : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · show (((1 / 2 : ℝ) : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I).im < 0
    simp
  · rw [mem_cruxV_iff]
    constructor
    · have hsub : ((1 / 2 : ℝ) : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I - 1
          = ((-(1 / 2) : ℝ) : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hsub]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, sub_zero,
        Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one, zero_sub]
      norm_num
    · show (((1 / 2 : ℝ) : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I).re < 1
      simp
      norm_num

/-- Norm bound used to build explicit witnesses in the half-discs. -/
private lemma norm_plus_I_le {t : ℝ} (ht : 0 ≤ t) :
    ‖((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I‖ ≤ 2 * t := by
  have hre : (((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re = -t := by simp
  have him : (((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im = t := by simp
  calc ‖((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I‖
      ≤ |(((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re|
        + |(((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |-t| + |t| := by rw [hre, him]
    _ = 2 * t := by rw [abs_neg, abs_of_nonneg ht]; ring

/-- Norm bound used to build explicit witnesses in the half-discs. -/
private lemma norm_sub_I_le {t : ℝ} (ht : 0 ≤ t) :
    ‖((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I‖ ≤ 2 * t := by
  have hre : (((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I).re = -t := by simp
  have him : (((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I).im = -t := by simp
  calc ‖((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I‖
      ≤ |(((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I).re|
        + |(((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |-t| + |-t| := by rw [hre, him]
    _ = 2 * t := by rw [abs_neg, abs_of_nonneg ht]; ring

/-- A point of `cruxU ∩ cruxV ∩ ball 1 δ` for every `δ > 0`. -/
theorem nonempty_cruxU_cruxV_ball (δ : ℝ) (hδ : 0 < δ) :
    (cruxU ∩ cruxV ∩ Metric.ball (1 : ℂ) δ).Nonempty := by
  set t : ℝ := min δ 1 / 4 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htδ : 2 * t < δ := by
    rw [ht]
    have : min δ 1 ≤ δ := min_le_left _ _
    linarith
  have ht8 : 2 * t < 8 / 9 := by
    rw [ht]
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  refine ⟨((1 - t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
  · show 0 < (((1 - t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im
    simp [ht0]
  · rw [mem_cruxV_iff]
    constructor
    · have hsub : ((1 - t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I - 1
          = ((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hsub]
      linarith [norm_plus_I_le ht0.le]
    · show (((1 - t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re < 1
      simp; linarith
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : ((1 - t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I - 1
        = ((-t : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]
    linarith [norm_plus_I_le ht0.le]

/-- A point of `cruxL ∩ cruxV ∩ ball 1 δ` for every `δ > 0`. -/
theorem nonempty_cruxL_cruxV_ball (δ : ℝ) (hδ : 0 < δ) :
    (cruxL ∩ cruxV ∩ Metric.ball (1 : ℂ) δ).Nonempty := by
  set t : ℝ := min δ 1 / 4 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htδ : 2 * t < δ := by
    rw [ht]
    have : min δ 1 ≤ δ := min_le_left _ _
    linarith
  have ht8 : 2 * t < 8 / 9 := by
    rw [ht]
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  refine ⟨((1 - t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
  · show (((1 - t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I).im < 0
    simp [ht0]
  · rw [mem_cruxV_iff]
    constructor
    · have hsub : ((1 - t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I - 1
          = ((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hsub]
      linarith [norm_sub_I_le ht0.le]
    · show (((1 - t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I).re < 1
      simp; linarith
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : ((1 - t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I - 1
        = ((-t : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]
    linarith [norm_sub_I_le ht0.le]

end

end Work.A14D
