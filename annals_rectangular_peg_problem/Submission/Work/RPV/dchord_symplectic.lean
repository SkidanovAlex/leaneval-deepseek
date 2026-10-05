import Mathlib
import Submission.Work.RPV.Defs

/-!
# The differential of the chord map is symplectic (`Work.RPV.dchord_symplectic`)

`dchord z w a ζ η` is the differential of the chord map `chordPS` at `(z,w)` (with `a` a lift of
`arg (z-w)`) in the direction `(ζ,η)`.  The node statement of the route design says that this
linearisation is compatible with the symplectic forms: with `ω = dp₁∧dq₁ + dp₂∧dq₂` on
`PS = ℝ⁴` and `ω_ℂ (x,y) = Im (conj x * y)` on `ℂ`,

`symp (dchord z w a ζ₁ η₁) (dchord z w a ζ₂ η₂) = ωC ζ₁ ζ₂ + ωC η₁ η₂`.

## Proof

Write `L = exp (-(a:ℂ) * I)` for the unitary factor (a rotation of the diagonal in `ℂ²`).
The proof has three ingredients, all of them elementary algebra:

* `dchord_rot`: replacing `(z,w,a)` by `(L*z, L*w, 0)` does not change `dchord` — the chord map is
  equivariant under a rotation of both coordinates together with the corresponding shift of the
  lift `a`.  Note `L * (z-w) = ‖z-w‖` by the hypothesis, so after this reduction the difference
  `z - w` is a *real* number.
* `ωC_exp_neg_I`: `ωC` is invariant under multiplication by the unitary factor `L`.
* `dchord_symp_zero`: the remaining computation, for `a = 0` and `w = z - r` with `r` real, is a
  polynomial identity which `field_simp` clears and `ring` discharges.

The hypothesis `ha : z - w = ‖z-w‖ • exp (a * I)` is exactly what is needed to know that
`L * (z - w) = ‖z - w‖` is a nonzero real number.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPV

open Complex

/-! ### Elementary facts about the unitary factor `exp (-aI)` -/

/-- The conjugate of `exp (-aI)` is `exp (aI)`. -/
lemma conj_exp_neg_I (a : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(a : ℂ) * I)) = Complex.exp ((a : ℂ) * I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]

/-- `exp (-aI)` is unitary: `conj (exp (-aI)) * exp (-aI) = 1`. -/
lemma conj_mul_exp_neg_I (a : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(a : ℂ) * I)) * Complex.exp (-(a : ℂ) * I) = 1 := by
  rw [conj_exp_neg_I, ← Complex.exp_add,
    show (a : ℂ) * I + -(a : ℂ) * I = 0 by ring, Complex.exp_zero]

/-- `exp (-aI) * exp (aI) = 1`. -/
lemma exp_neg_I_mul (a : ℝ) :
    Complex.exp (-(a : ℂ) * I) * Complex.exp ((a : ℂ) * I) = 1 := by
  rw [← Complex.exp_add, show -(a : ℂ) * I + (a : ℂ) * I = 0 by ring, Complex.exp_zero]

/-- The unitary factor at `a = 0` is `1`. -/
lemma exp_zero_I : Complex.exp (-((0 : ℝ) : ℂ) * I) = 1 := by
  norm_num [Complex.exp_zero]

/-! ### Rotation equivariance of the chord differential -/

/-- The chord differential is equivariant under the diagonal rotation
`(z, w, a) ↦ (exp (-aI) z, exp (-aI) w, 0)`.  This is the reduction that makes the difference
of the two points a real number. -/
lemma dchord_rot (z w : ℂ) (a : ℝ) (ζ η : ℂ) :
    dchord z w a ζ η =
      dchord (Complex.exp (-(a : ℂ) * I) * z) (Complex.exp (-(a : ℂ) * I) * w) 0
        (Complex.exp (-(a : ℂ) * I) * ζ) (Complex.exp (-(a : ℂ) * I) * η) := by
  set L : ℂ := Complex.exp (-(a : ℂ) * I) with hL
  have hL0 : L ≠ 0 := by rw [hL]; exact Complex.exp_ne_zero _
  have hunit : (starRingEnd ℂ) L * L = 1 := by rw [hL]; exact conj_mul_exp_neg_I a
  have hexp0 : Complex.exp (-((0 : ℝ) : ℂ) * I) = 1 := exp_zero_I
  simp only [dchord]
  rw [← hL]
  have hdiv : (L * ζ - L * η) / (L * z - L * w) = (ζ - η) / (z - w) := by
    rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hL0]
  have hdu : Complex.exp (-((0 : ℝ) : ℂ) * I) * ((L * ζ + L * η) / (Real.sqrt 2 : ℂ) -
        ((L * ζ - L * η) / (L * z - L * w)).im * I * ((L * z + L * w) / (Real.sqrt 2 : ℂ)))
      = L * ((ζ + η) / (Real.sqrt 2 : ℂ) -
        ((ζ - η) / (z - w)).im * I * ((z + w) / (Real.sqrt 2 : ℂ))) := by
    rw [hdiv, hexp0, one_mul, ← mul_add, ← mul_add, mul_div_assoc, mul_div_assoc]
    ring
  have hP1 : (starRingEnd ℂ) (L * z) * (L * ζ) = (starRingEnd ℂ) z * ζ := by
    rw [map_mul]
    rw [show (starRingEnd ℂ) L * (starRingEnd ℂ) z * (L * ζ)
        = ((starRingEnd ℂ) L * L) * ((starRingEnd ℂ) z * ζ) by ring, hunit, one_mul]
  have hP2 : (starRingEnd ℂ) (L * w) * (L * η) = (starRingEnd ℂ) w * η := by
    rw [map_mul]
    rw [show (starRingEnd ℂ) L * (starRingEnd ℂ) w * (L * η)
        = ((starRingEnd ℂ) L * L) * ((starRingEnd ℂ) w * η) by ring, hunit, one_mul]
  rw [hdu, hP1, hP2, hdiv]

/-- `ωC` is invariant under multiplication by the unitary factor `exp (-aI)`. -/
lemma ωC_exp_neg_I (a : ℝ) (ζ₁ ζ₂ : ℂ) :
    ωC (Complex.exp (-(a : ℂ) * I) * ζ₁) (Complex.exp (-(a : ℂ) * I) * ζ₂) = ωC ζ₁ ζ₂ := by
  set L : ℂ := Complex.exp (-(a : ℂ) * I) with hL
  have hunit : (starRingEnd ℂ) L * L = 1 := by rw [hL]; exact conj_mul_exp_neg_I a
  have h : (starRingEnd ℂ) (L * ζ₁) * (L * ζ₂) = (starRingEnd ℂ) ζ₁ * ζ₂ := by
    rw [map_mul]
    rw [show (starRingEnd ℂ) L * (starRingEnd ℂ) ζ₁ * (L * ζ₂)
        = ((starRingEnd ℂ) L * L) * ((starRingEnd ℂ) ζ₁ * ζ₂) by ring, hunit, one_mul]
  simp only [ωC]
  rw [h]

/-! ### The computation at the normalised point -/

/-- The heart of the matter: for a pair whose difference is a nonzero *real* number the
differential of the chord map is symplectic.  Everything is a polynomial identity in the real
coordinates once the denominators are cleared, so `field_simp` and `ring` suffice. -/
lemma dchord_symp_zero (z : ℂ) (r : ℝ) (hr : r ≠ 0) (ζ₁ η₁ ζ₂ η₂ : ℂ) :
    symp (dchord z (z - (r : ℂ)) 0 ζ₁ η₁) (dchord z (z - (r : ℂ)) 0 ζ₂ η₂)
      = ωC ζ₁ ζ₂ + ωC η₁ η₂ := by
  have hzr : z - (z - (r : ℂ)) = (r : ℂ) := by ring
  have hexp : Complex.exp (-((0 : ℝ) : ℂ) * I) = 1 := exp_zero_I
  simp only [dchord]
  rw [hzr, hexp]
  simp only [symp, ωC, one_mul, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  have h2s : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [h2s]
  ring

/-! ### The node statement -/

theorem dchord_symplectic (z w : ℂ) (a : ℝ) (hzw : z ≠ w)
    (ha : z - w = (‖z - w‖ : ℂ) * Complex.exp (a * I)) (ζ₁ η₁ ζ₂ η₂ : ℂ) :
    Work.RPV.symp (Work.RPV.dchord z w a ζ₁ η₁) (Work.RPV.dchord z w a ζ₂ η₂)
      = Work.RPV.ωC ζ₁ ζ₂ + Work.RPV.ωC η₁ η₂ := by
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hr : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.mpr hzw'
  have hlam : Complex.exp (-(a : ℂ) * I) * (z - w) = ((‖z - w‖ : ℝ) : ℂ) := by
    conv_lhs => rw [ha]
    rw [show Complex.exp (-(a : ℂ) * I) * (((‖z - w‖ : ℝ) : ℂ) * Complex.exp (a * I))
        = ((‖z - w‖ : ℝ) : ℂ) * (Complex.exp (-(a : ℂ) * I) * Complex.exp (a * I)) by ring,
      exp_neg_I_mul a, mul_one]
  have hsub : Complex.exp (-(a : ℂ) * I) * z - Complex.exp (-(a : ℂ) * I) * w
      = ((‖z - w‖ : ℝ) : ℂ) := by
    rw [← mul_sub]
    exact hlam
  have hw' : Complex.exp (-(a : ℂ) * I) * w
      = Complex.exp (-(a : ℂ) * I) * z - ((‖z - w‖ : ℝ) : ℂ) := by
    rw [← hsub]
    ring
  rw [dchord_rot z w a ζ₁ η₁, dchord_rot z w a ζ₂ η₂, hw']
  rw [dchord_symp_zero (Complex.exp (-(a : ℂ) * I) * z) ‖z - w‖ hr
    (Complex.exp (-(a : ℂ) * I) * ζ₁) (Complex.exp (-(a : ℂ) * I) * η₁)
    (Complex.exp (-(a : ℂ) * I) * ζ₂) (Complex.exp (-(a : ℂ) * I) * η₂)]
  rw [ωC_exp_neg_I a ζ₁ ζ₂, ωC_exp_neg_I a η₁ η₂]

end Work.RPV
