/-
# `Work.FIArea3.JointCount.sweep_defs`

Definitions for the convex sweep-volume bound `Work.FIArea3.JointCount.convex_sweep_volume`.

The functional `wid z` is the one appearing in the target statement (namely `w ↦ ⟨w, z * I⟩`), and
`hmap z` is the `ℝ`-linear map
  `w ↦ Re (w * conj z)/‖z‖² + Im (w * conj z) * I`,
whose determinant has absolute value `1` (it is a measure preserving sheared rotation): it sends
the segment `[0,z]` onto the real unit segment `[0,1]` and satisfies `(hmap z w).im = wid z w`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The linear functional `w ↦ ⟨w, z * I⟩ = w.re * (z * I).re + w.im * (z * I).im`, exactly as in
the statement of `convex_sweep_volume`. -/
def wid (z w : ℂ) : ℝ := w.re * (z * Complex.I).re + w.im * (z * Complex.I).im

/-- The closed segment from `0` to `z`. -/
def segz (z : ℂ) : Set ℂ := {w : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, w = t • z}

/-- The real unit segment `[0,1]` inside `ℂ`. -/
def unitSeg : Set ℂ := {w : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, w = (t : ℂ)}

/-- The identity `⟨w, z * I⟩ = Im (w * conj z)`. -/
lemma wid_eq_im_mul_conj (z w : ℂ) : wid z w = (w * star z).im := by
  simp only [wid, Complex.star_def, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Multiplication by `conj z`, as an `ℝ`-linear self-map of `ℂ`. -/
def mulConjZ (z : ℂ) : ℂ →ₗ[ℝ] ℂ := Llc (star z) (star z * Complex.I)

/-- The diagonal scaling `x + yi ↦ x * c + yi`. -/
def diagScale (c : ℝ) : ℂ →ₗ[ℝ] ℂ := Llc (c : ℂ) Complex.I

/-- The sheared rotation `w ↦ Re (w * conj z)/‖z‖² + Im (w * conj z) * I`. -/
def hmap (z : ℂ) : ℂ →ₗ[ℝ] ℂ := (diagScale (1 / Complex.normSq z)).comp (mulConjZ z)

@[simp] lemma mulConjZ_apply (z w : ℂ) : mulConjZ z w = w * star z := by
  rw [mulConjZ, Llc_apply]
  refine Complex.ext ?_ ?_ <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.star_def]

@[simp] lemma diagScale_apply (c : ℝ) (q : ℂ) :
    diagScale c q = (((q.re * c : ℝ)) : ℂ) + (((q.im : ℝ)) : ℂ) * Complex.I := by
  rw [diagScale, Llc_apply]
  refine Complex.ext ?_ ?_ <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]

lemma det_mulConjZ (z : ℂ) : LinearMap.det (mulConjZ z) = Complex.normSq z := by
  rw [mulConjZ, Llc_det, Complex.normSq_apply]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, sub_zero, zero_add]
  ring

lemma det_diagScale (c : ℝ) : LinearMap.det (diagScale c) = c := by
  rw [diagScale, Llc_det]
  simp [Complex.star_def]

lemma hmap_apply (z w : ℂ) :
    hmap z w = ((((w * star z).re / Complex.normSq z : ℝ)) : ℂ)
      + ((((w * star z).im : ℝ)) : ℂ) * Complex.I := by
  rw [hmap, LinearMap.comp_apply, diagScale_apply, mulConjZ_apply]
  congr 1
  rw [mul_one_div]

lemma hmap_im (z w : ℂ) : (hmap z w).im = wid z w := by
  rw [hmap_apply, ← wid_eq_im_mul_conj]
  simp [Complex.add_im, Complex.mul_im]

lemma hmap_self (z : ℂ) (hz : z ≠ 0) : hmap z z = 1 := by
  have hne : (Complex.normSq z : ℂ) ≠ 0 := by
    simpa using (Complex.normSq_pos.mpr hz).ne'
  have hre : (z * star z).re = Complex.normSq z := by
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  have him : (z * star z).im = 0 := by
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  rw [hmap_apply, hre, him, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_div,
    div_self hne]

lemma lipschitz_Llc (u v : ℂ) : LipschitzWith (‖u‖₊ + ‖v‖₊) (Llc u v) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro a b
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, Llc_apply]
  have h1 : |(a - b).re| ≤ ‖a - b‖ := Complex.abs_re_le_norm _
  have h2 : |(a - b).im| ≤ ‖a - b‖ := Complex.abs_im_le_norm _
  calc ‖(a - b).re • u + (a - b).im • v‖ ≤ ‖(a - b).re • u‖ + ‖(a - b).im • v‖ := norm_add_le _ _
    _ = |(a - b).re| * ‖u‖ + |(a - b).im| * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖a - b‖ * ‖u‖ + ‖a - b‖ * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = (↑(‖u‖₊ + ‖v‖₊) : ℝ) * ‖a - b‖ := by push_cast; ring

lemma isBounded_mulConjZ (z : ℂ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    Bornology.IsBounded (mulConjZ z '' X) :=
  (lipschitz_Llc (star z) (star z * Complex.I)).isBounded_image hX

lemma isBounded_diagScale (c : ℝ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    Bornology.IsBounded (diagScale c '' X) :=
  (lipschitz_Llc (c : ℂ) Complex.I).isBounded_image hX

lemma hmap_image_eq (z : ℂ) (X : Set ℂ) :
    hmap z '' X = diagScale (1 / Complex.normSq z) '' (mulConjZ z '' X) := by
  rw [hmap, LinearMap.coe_comp, Set.image_comp]

lemma isBounded_hmap (z : ℂ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    Bornology.IsBounded (hmap z '' X) := by
  rw [hmap_image_eq]
  exact isBounded_diagScale _ (isBounded_mulConjZ z hX)

end

end Work.FIArea3.JointCount
