import Mathlib
import Submission.Work.KT.Fund.kappa_hopf_defs

/-!
# `Work.KT.Fund.kappa_hopf_pulldn`

Restriction of the Hopf idempotent `hopfMat` (pulled back from `S²` along the second projection of
`X × S²`) to the lower disc `X × D`, computed in the disc coordinates.

The lower hemisphere parametrisation is `dn v = (v.re, v.im, -√(1-‖v‖²)) ∈ S²`.  Evaluating the
entries of `(1/2) · (1 + x₀σ₁ + x₁σ₂ + x₃σ₃)` at `dn v` gives, with `c = cCoord = v` and
`s = cHeight = √(1-‖v‖²)`,

* `(0,0)`: `(1/2) (1 - s)`,
* `(0,1)`: `(1/2) (v.re - i v.im) = (1/2) (star v)`,
* `(1,0)`: `(1/2) (v.re + i v.im) = (1/2) v`,
* `(1,1)`: `(1/2) (1 + s)`.

This is the disc-matrix component of the class `snd^*(cls hopfIdem)` used in the proof of
Bott periodicity / `kappa_hopf`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

/-- The star of a complex number, in terms of its real and imaginary parts. -/
lemma starC_eq_re_sub_im (v : ℂ) : (starRingEnd ℂ) v = ↑v.re - ↑v.im * Complex.I := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]

/-- Elementary complex identities for the four entries. -/
lemma halfC_aux00 (s : ℝ) : (2 : ℂ)⁻¹ + -(2⁻¹ * (s : ℂ)) = (1 - (s : ℂ)) * (2 : ℂ)⁻¹ := by ring
lemma halfC_aux11 (s : ℝ) : (2 : ℂ)⁻¹ * (1 + (s : ℂ)) = (1 + (s : ℂ)) * (2 : ℂ)⁻¹ := by ring
lemma halfC_aux01 (v : ℂ) :
    (2 : ℂ)⁻¹ * (↑v.re - Complex.I * ↑v.im) = (starRingEnd ℂ) v * (2 : ℂ)⁻¹ := by
  rw [starC_eq_re_sub_im]; ring
lemma halfC_aux10 (v : ℂ) :
    (2 : ℂ)⁻¹ * ↑v.re + (2 : ℂ)⁻¹ * (Complex.I * ↑v.im) = v * (2 : ℂ)⁻¹ := by
  conv_rhs => rw [← Complex.re_add_im v]
  ring

theorem kappa_hopf_pulldn (X : Type) [TopologicalSpace X] :
    (hopfMat.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom).map (pullDn X)
      = !![(1 - cHeight X) * halfC X, star (cCoord X) * halfC X;
           cCoord X * halfC X, (1 + cHeight X) * halfC X] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hopfMat, Matrix.map_apply, coordC, cCoord, cHeight, halfC, pullDn_apply, dn, dnPt,
      mk3, ContinuousMap.star_apply]
  · exact halfC_aux00 _
  · exact halfC_aux01 _
  · exact halfC_aux10 _
  · exact halfC_aux11 _

end

end Work.KT.Fund
