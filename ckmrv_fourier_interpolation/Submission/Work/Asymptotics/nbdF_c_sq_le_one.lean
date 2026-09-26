/-
# The `(1,0)`-entry of a matrix taking `nbdF` into itself is `±1` or `0`

If `z` and `γ • z` both lie in the thickened fundamental domain `nbdF` of
`Submission.Work.Asymptotics.DomainFThickening`, then the lower-left entry `γ 1 0` of
`γ ∈ SL(2,ℤ)` has square `≤ 1`, i.e. `γ 1 0 ∈ {-1, 0, 1}`.

The proof is the elementary "imaginary part" argument.  For `γ = !![a,b;c,d]` and
`w = γ • z` one has

  `Im w = Im z / ‖c z + d‖²`   (`ModularGroup.im_smul_eq_div_normSq`).

Every point of `nbdF` has imaginary part `> 3/4`, so if `|c| ≥ 2` then

  `‖c z + d‖² ≥ (c · Im z)² > (2 · 3/4)² = 9/4 > 1`,

whence `Im w < Im z`.  Applying the same bound to `γ⁻¹` (whose `(1,0)`-entry is `-c`, so has the
same absolute value) at the point `w`, one gets `Im z < Im w` as well, a contradiction.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainFThickening

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups

namespace Work.Asymptotics

/-- The norm-square of the denominator `c z + d` of the Möbius transform `γ`, written in terms
of the real and imaginary parts of `z` and of the entries of `γ`. -/
lemma nbdF_normSq_denom (γ : SL(2,ℤ)) (z : ℍ) :
    Complex.normSq (denom γ z) =
      ((γ 1 0 : ℝ) * z.re + (γ 1 1 : ℝ)) ^ 2 + ((γ 1 0 : ℝ) * z.im) ^ 2 := by
  rw [ModularGroup.denom_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- If `z ∈ nbdF` and `|c| ≥ 2` is an integer, then `‖c z + d‖² > 1` for any integer `d`.
Indeed `Im z > 3/4`, so `‖c z + d‖² ≥ (c · Im z)² > (3/2)² > 1`. -/
lemma nbdF_one_lt_normSq_pair {z : ℍ} (hz : z ∈ nbdF) {c d : ℤ} (hc : 2 ≤ |c|) :
    1 < ((c : ℝ) * z.re + (d : ℝ)) ^ 2 + ((c : ℝ) * z.im) ^ 2 := by
  have him : (3 / 4 : ℝ) < z.im := im_gt_of_mem_nbdF hz
  have hcR : (2 : ℝ) ≤ |(c : ℝ)| := by
    rw [← Int.cast_abs (R := ℝ) (a := c)]
    exact_mod_cast hc
  have h2 : (3 / 2 : ℝ) < |(c : ℝ) * z.im| := by
    rw [abs_mul, abs_of_pos z.im_pos]
    nlinarith [abs_nonneg (c : ℝ)]
  have h3 : (3 / 2 : ℝ) ^ 2 < ((c : ℝ) * z.im) ^ 2 := by
    rw [← sq_abs ((c : ℝ) * z.im)]
    nlinarith [abs_nonneg ((c : ℝ) * z.im)]
  nlinarith [sq_nonneg ((c : ℝ) * z.re + (d : ℝ))]

theorem nbdF_c_sq_le_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {z : UpperHalfPlane}
    (hz : z ∈ Work.Asymptotics.nbdF) (hw : γ • z ∈ Work.Asymptotics.nbdF) :
    (γ 1 0) ^ 2 ≤ 1 := by
  by_contra h
  have hc_sq : (1 : ℤ) < (γ 1 0) ^ 2 := lt_of_not_ge h
  have hc_abs : (1 : ℤ) < |γ 1 0| := by
    nlinarith [sq_abs (γ 1 0), abs_nonneg (γ 1 0)]
  have hc2 : (2 : ℤ) ≤ |γ 1 0| := by omega
  set w : ℍ := γ • z with hwdef
  have hw' : w ∈ nbdF := by rw [hwdef]; exact hw
  have hinv : γ⁻¹ • w = z := by rw [hwdef]; exact inv_smul_smul γ z
  have hN1 : (1 : ℝ) < Complex.normSq (denom γ z) := by
    rw [nbdF_normSq_denom γ z]
    exact nbdF_one_lt_normSq_pair hz hc2
  have hcinv : (γ⁻¹ : SL(2,ℤ)) 1 0 = -(γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
  have hc2inv : (2 : ℤ) ≤ |(γ⁻¹ : SL(2,ℤ)) 1 0| := by rw [hcinv, abs_neg]; exact hc2
  have hN2 : (1 : ℝ) < Complex.normSq (denom (γ⁻¹ : SL(2,ℤ)) w) := by
    rw [nbdF_normSq_denom (γ⁻¹ : SL(2,ℤ)) w]
    exact nbdF_one_lt_normSq_pair hw' hc2inv
  have hstep1 : w.im = z.im / Complex.normSq (denom γ z) := by
    rw [hwdef]; exact ModularGroup.im_smul_eq_div_normSq γ z
  have hstep2 : z.im = w.im / Complex.normSq (denom (γ⁻¹ : SL(2,ℤ)) w) := by
    have hh := ModularGroup.im_smul_eq_div_normSq (γ⁻¹ : SL(2,ℤ)) w
    rw [hinv] at hh
    exact hh
  have h1 : w.im < z.im := by
    rw [hstep1, div_lt_iff₀ (by linarith : (0 : ℝ) < Complex.normSq (denom γ z))]
    nlinarith [z.im_pos]
  have h2 : z.im < w.im := by
    rw [hstep2,
      div_lt_iff₀ (by linarith : (0 : ℝ) < Complex.normSq (denom (γ⁻¹ : SL(2,ℤ)) w))]
    nlinarith [w.im_pos]
  linarith

end Work.Asymptotics
