import Mathlib
import Submission.Work.A14D.setup

/-!
# A14D: the three convex pieces of the slit disc

The slit disc `slitDisk δ = ball (1/9) δ ∩ slitComp` is the union of the three basic convex
pieces

* `halfUp δ = ball (1/9) δ ∩ {Im > 0}` (upper half-disc),
* `halfDn δ = ball (1/9) δ ∩ {Im < 0}` (lower half-disc),
* `halfRt δ = ball (1/9) δ ∩ {Re > 1/9}` (right half-disc),

which are all convex and open, contained in the slit disc, and glued as
`halfUp ∩ halfRt ≠ ∅`, `halfDn ∩ halfRt ≠ ∅`, `halfUp ∩ halfDn = ∅`.  This is the cover used
to continue a solution of `LZ = 0` from a convex piece to the whole slit disc.
-/

namespace Work.A14D

open Complex Metric
open scoped Topology

noncomputable section

/-- The upper half-disc: `ball (1/9) δ ∩ {Im > 0}`. -/
def halfUp (δ : ℝ) : Set ℂ := Metric.ball ninth δ ∩ {z : ℂ | 0 < z.im}

/-- The lower half-disc: `ball (1/9) δ ∩ {Im < 0}`. -/
def halfDn (δ : ℝ) : Set ℂ := Metric.ball ninth δ ∩ {z : ℂ | z.im < 0}

/-- The right half-disc: `ball (1/9) δ ∩ {Re > 1/9}`. -/
def halfRt (δ : ℝ) : Set ℂ := Metric.ball ninth δ ∩ {z : ℂ | ninth.re < z.re}

lemma ninth_re : ninth.re = 1 / 9 := by simp [ninth]

lemma ninth_im : ninth.im = 0 := by simp [ninth]

lemma ninth_eq : ninth = ((1/9 : ℝ) : ℂ) := by rw [ninth]; norm_num

lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma norm_ofReal_nonneg {r : ℝ} (h : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  rw [norm_ofReal_eq_abs, abs_of_nonneg h]

lemma norm_ofReal_mul_I_nonneg {r : ℝ} (h : 0 ≤ r) : ‖((r : ℝ) : ℂ) * Complex.I‖ = r := by
  rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_nonneg h]

lemma mem_halfUp_iff {δ : ℝ} {z : ℂ} : z ∈ halfUp δ ↔ z ∈ Metric.ball ninth δ ∧ 0 < z.im :=
  Iff.rfl

lemma mem_halfDn_iff {δ : ℝ} {z : ℂ} : z ∈ halfDn δ ↔ z ∈ Metric.ball ninth δ ∧ z.im < 0 :=
  Iff.rfl

lemma mem_halfRt_iff {δ : ℝ} {z : ℂ} :
    z ∈ halfRt δ ↔ z ∈ Metric.ball ninth δ ∧ 1 / 9 < z.re := by
  rw [halfRt, Set.mem_inter_iff, Set.mem_setOf_eq, ninth_re]

lemma isOpen_halfUp (δ : ℝ) : IsOpen (halfUp δ) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

lemma isOpen_halfDn (δ : ℝ) : IsOpen (halfDn δ) :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)

lemma isOpen_halfRt (δ : ℝ) : IsOpen (halfRt δ) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

lemma convex_halfUp (δ : ℝ) : Convex ℝ (halfUp δ) :=
  (convex_ball ninth δ).inter (convex_halfSpace_im_gt 0)

lemma convex_halfDn (δ : ℝ) : Convex ℝ (halfDn δ) :=
  (convex_ball ninth δ).inter (convex_halfSpace_im_lt 0)

lemma convex_halfRt (δ : ℝ) : Convex ℝ (halfRt δ) :=
  (convex_ball ninth δ).inter (convex_halfSpace_re_gt ninth.re)

lemma halfUp_subset_slitDisk (δ : ℝ) : halfUp δ ⊆ slitDisk δ :=
  fun z hz => ⟨hz.1, Or.inl (ne_of_gt hz.2)⟩

lemma halfDn_subset_slitDisk (δ : ℝ) : halfDn δ ⊆ slitDisk δ :=
  fun z hz => ⟨hz.1, Or.inl (ne_of_lt hz.2)⟩

lemma halfRt_subset_slitDisk (δ : ℝ) : halfRt δ ⊆ slitDisk δ :=
  fun z hz => ⟨hz.1, Or.inr hz.2⟩

lemma slitDisk_subset_union (δ : ℝ) : slitDisk δ ⊆ halfUp δ ∪ halfDn δ ∪ halfRt δ := by
  intro z hz
  rw [mem_slitDisk_iff] at hz
  obtain ⟨hb, h⟩ := hz
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · exact Or.inl (Or.inr ⟨hb, hlt⟩)
  · rcases h with h | h
    · exact absurd heq h
    · exact Or.inr ⟨hb, h⟩
  · exact Or.inl (Or.inl ⟨hb, hgt⟩)

lemma halfUp_inter_halfDn (δ : ℝ) : halfUp δ ∩ halfDn δ = ∅ := by
  ext z
  simp only [halfUp, halfDn, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  exact ⟨fun h => absurd h.2.2 (not_lt.mpr h.1.2.le), fun h => h.elim⟩

lemma halfUp_nonempty {δ : ℝ} (hδ : 0 < δ) : (halfUp δ).Nonempty := by
  refine ⟨((1/9 : ℝ) : ℂ) + ((δ / 4 : ℝ) : ℂ) * Complex.I, ?_⟩
  simp only [halfUp, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ninth_eq]
    have hsub : ((1/9 : ℝ) : ℂ) + ((δ/4 : ℝ) : ℂ) * Complex.I - ((1/9 : ℝ) : ℂ)
        = ((δ/4 : ℝ) : ℂ) * Complex.I := by ring
    rw [hsub, norm_ofReal_mul_I_nonneg (by linarith : (0:ℝ) ≤ δ/4)]
    linarith
  · simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im, Complex.ofReal_re]
    linarith

lemma halfRt_nonempty {δ : ℝ} (hδ : 0 < δ) : (halfRt δ).Nonempty := by
  refine ⟨((1/9 + δ/2 : ℝ) : ℂ), ?_⟩
  simp only [halfRt, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ninth_eq]
    have hsub : ((1/9 + δ/2 : ℝ) : ℂ) - ((1/9 : ℝ) : ℂ) = ((δ/2 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, norm_ofReal_nonneg (by linarith : (0:ℝ) ≤ δ/2)]
    linarith
  · simp only [ninth_re, Complex.ofReal_re]
    linarith

lemma halfUp_inter_halfRt_nonempty {δ : ℝ} (hδ : 0 < δ) :
    (halfUp δ ∩ halfRt δ).Nonempty := by
  have hr : (0:ℝ) ≤ δ / 20 := by linarith
  refine ⟨((1/9 + δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I, ?_⟩
  simp only [halfUp, halfRt, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ninth_eq]
    have hsub : ((1/9 + δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I - ((1/9 : ℝ) : ℂ)
        = ((δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]
    calc ‖((δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((δ/20 : ℝ) : ℂ)‖ + ‖((δ/20 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = δ/20 + δ/20 := by rw [norm_ofReal_nonneg hr, norm_ofReal_mul_I_nonneg hr]
      _ < δ := by linarith
  · simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im, Complex.ofReal_re]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm, ninth_eq]
    have hsub : ((1/9 + δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I - ((1/9 : ℝ) : ℂ)
        = ((δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]
    calc ‖((δ/20 : ℝ) : ℂ) + ((δ/20 : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((δ/20 : ℝ) : ℂ)‖ + ‖((δ/20 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = δ/20 + δ/20 := by rw [norm_ofReal_nonneg hr, norm_ofReal_mul_I_nonneg hr]
      _ < δ := by linarith
  · simp only [ninth_re, Complex.add_re, Complex.mul_I_re, Complex.ofReal_re, Complex.ofReal_im]
    linarith

lemma halfDn_inter_halfRt_nonempty {δ : ℝ} (hδ : 0 < δ) :
    (halfDn δ ∩ halfRt δ).Nonempty := by
  have hr : (0:ℝ) ≤ δ / 20 := by linarith
  refine ⟨((1/9 + δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I, ?_⟩
  simp only [halfDn, halfRt, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ninth_eq]
    have hsub : ((1/9 + δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I - ((1/9 : ℝ) : ℂ)
        = ((δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]
    calc ‖((δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((δ/20 : ℝ) : ℂ)‖ + ‖((δ/20 : ℝ) : ℂ) * Complex.I‖ := by
          simpa using norm_sub_le (((δ/20 : ℝ) : ℂ)) (((δ/20 : ℝ) : ℂ) * Complex.I)
      _ = δ/20 + δ/20 := by rw [norm_ofReal_nonneg hr, norm_ofReal_mul_I_nonneg hr]
      _ < δ := by linarith
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_im, Complex.ofReal_re]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm, ninth_eq]
    have hsub : ((1/9 + δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I - ((1/9 : ℝ) : ℂ)
        = ((δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]
    calc ‖((δ/20 : ℝ) : ℂ) - ((δ/20 : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((δ/20 : ℝ) : ℂ)‖ + ‖((δ/20 : ℝ) : ℂ) * Complex.I‖ := by
          simpa using norm_sub_le (((δ/20 : ℝ) : ℂ)) (((δ/20 : ℝ) : ℂ) * Complex.I)
      _ = δ/20 + δ/20 := by rw [norm_ofReal_nonneg hr, norm_ofReal_mul_I_nonneg hr]
      _ < δ := by linarith
  · simp only [ninth_re, Complex.sub_re, Complex.mul_I_re, Complex.ofReal_re, Complex.ofReal_im]
    linarith

end

end Work.A14D
