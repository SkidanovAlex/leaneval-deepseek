import Mathlib
import Submission.Work.Asymptotics.DomainFThickening

noncomputable section

open UpperHalfPlane Matrix

namespace Work.Asymptotics

/-- For a matrix `γ ∈ SL(2, ℤ)` whose lower-left entry is `-1`, the (squared modulus of the)
denominator `c z + d` of the associated Möbius transformation equals `(d - Re z)² + (Im z)²`.
Here `c = γ 1 0 = -1` and `d = γ 1 1`. -/
lemma normSq_denom_eq_of_apply_one_zero_eq_neg_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {z : UpperHalfPlane} (hc : γ 1 0 = -1) :
    Complex.normSq (UpperHalfPlane.denom
        (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
        (z : ℂ)) = (((γ 1 1 : ℤ) : ℝ) - z.re) ^ 2 + z.im ^ 2 := by
  rw [ModularGroup.denom_apply, hc]
  simp only [Int.cast_neg, Int.cast_one]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- If both `z` and `γ • z` lie in the `1/16`-thickening `nbdF` of `closure 𝓕` and `γ` has
lower-left entry `-1`, then the lower-right entry `d = γ 1 1` is very close to `Re z`, namely
`(d - Re z)² < 7/16`.

The proof only uses the imaginary part bounds coming from `nbdF`: writing `w = γ • z`, the
Möbius formula gives `Im w = Im z / ((d - Re z)² + (Im z)²)`, and `Im w > 3/4` together with
`Im z > 3/4` forces `(d - Re z)² < (4/3) Im z - (Im z)² < 7/16`. -/
theorem nbdF_re_sub_sq_lt {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {z : UpperHalfPlane}
    (hz : z ∈ Work.Asymptotics.nbdF) (hw : γ • z ∈ Work.Asymptotics.nbdF) (hc : γ 1 0 = -1) :
    (((γ 1 1 : ℤ) : ℝ) - z.re) ^ 2 < 7 / 16 := by
  have hz_im : (3 / 4 : ℝ) < z.im := im_gt_of_mem_nbdF hz
  have hw_im : (3 / 4 : ℝ) < (γ • z).im := im_gt_of_mem_nbdF hw
  rw [ModularGroup.im_smul_eq_div_normSq,
    normSq_denom_eq_of_apply_one_zero_eq_neg_one hc] at hw_im
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hd
  have hpos : 0 < (d - z.re) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg (d - z.re), z.im_pos]
  rw [lt_div_iff₀ hpos] at hw_im
  have hmain : (d - z.re) ^ 2 + z.im ^ 2 < 4 / 3 * z.im := by nlinarith [hw_im]
  have key : (4 / 3 : ℝ) * z.im - z.im ^ 2 < 7 / 16 := by
    nlinarith [mul_pos (show (0 : ℝ) < z.im - 3 / 4 by linarith)
      (show (0 : ℝ) < z.im - 7 / 12 by linarith)]
  rw [hd]
  nlinarith [hmain, key]

end Work.Asymptotics
