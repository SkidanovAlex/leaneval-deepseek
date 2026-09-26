import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs

/-!
# The contour point `i t` as a total function, and the bridge to `Kax`

The parametric integrals of `LamDefs` are written with `Kax K τ x t`, which is `K τ (x +ᵢ t)`
for `t > 0` and `0` otherwise (the junk convention).  For statements about continuity,
measurability and analyticity it is convenient to have the contour point as an honest *total*
function of `t`:

  `zcb t = ofComplex (t * I)`,

which agrees with `Work.Kernels.imagAxis t ht` for `t > 0` and is (junk-)continuous there.
This file records that point and the elementary rewriting lemmas.
-/

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory

/-- The contour point `i t`, as a total function of `t` (the value is junk for `t ≤ 0`). -/
def zcb (t : ℝ) : UpperHalfPlane := UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I)

/-- `zcb` is continuous on `(0,∞)`. -/
lemma continuousOn_zcb : ContinuousOn zcb (Set.Ioi (0 : ℝ)) := by
  have h : zcb = fun t : ℝ => UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) := by
    funext t
    rw [zcb]; congr 1; ring
  rw [h]
  exact UpperHalfPlane.continuousOn_ofComplex_I_mul

/-- For `t > 0` the total point `zcb t` is the familiar `imagAxis t`. -/
lemma zcb_eq_imagAxis {t : ℝ} (ht : 0 < t) : zcb t = Work.Kernels.imagAxis t ht := by
  have him : 0 < ((t : ℂ) * Complex.I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simpa using ht
  apply UpperHalfPlane.ext
  rw [zcb, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  rfl

/-- `Kax` at a positive height is the kernel evaluated at `x + i t`. -/
lemma Kax_eq (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) {x t : ℝ}
    (ht : 0 < t) : Kax K τ x t = K τ ((x : ℝ) +ᵥ zcb t) := by
  rw [Kax, dif_pos ht]
  exact congrArg (K τ) (congrArg (fun w => (x : ℝ) +ᵥ w) (zcb_eq_imagAxis ht).symm)

/-- The coercion of `zcb t` is `t * I` for `t > 0`. -/
lemma zcb_coe {t : ℝ} (ht : 0 < t) : ((zcb t : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := by
  have him : 0 < ((t : ℂ) * Complex.I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simpa using ht
  rw [zcb, UpperHalfPlane.ofComplex_apply_of_im_pos him]

/-- The imaginary part of `zcb t` is `t` for `t > 0`. -/
lemma zcb_im {t : ℝ} (ht : 0 < t) : (zcb t).im = t := by
  rw [← UpperHalfPlane.coe_im, zcb_coe ht]
  simp

/-- The real part of `zcb t` is `0` for `t > 0`. -/
lemma zcb_re {t : ℝ} (ht : 0 < t) : (zcb t).re = 0 := by
  rw [← UpperHalfPlane.coe_re, zcb_coe ht]
  simp

/-- `S` acts on the contour point by `i t ↦ i/t`. -/
lemma S_smul_zcb {t : ℝ} (ht : 0 < t) : ModularGroup.S • zcb t = zcb t⁻¹ := by
  have h1 : ModularGroup.S • zcb t
      = UpperHalfPlane.mk (-(zcb t : ℂ))⁻¹ (UpperHalfPlane.im_inv_neg_coe_pos (zcb t)) :=
    UpperHalfPlane.modular_S_smul (zcb t)
  rw [h1, UpperHalfPlane.ext_iff]
  simp only [UpperHalfPlane.coe_mk]
  rw [zcb_coe ht, zcb_coe (inv_pos.mpr ht), inv_neg, mul_inv]
  push_cast
  rw [Complex.inv_I]
  ring

/-- The contour point at height `1` is `i`. -/
lemma zcb_one : zcb 1 = Work.Kernels.imagAxis 1 one_pos := zcb_eq_imagAxis one_pos

end Work.CKFinal.LineDecay
