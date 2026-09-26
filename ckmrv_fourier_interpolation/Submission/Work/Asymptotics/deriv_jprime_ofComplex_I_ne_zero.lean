import Mathlib
import Submission.Work.Asymptotics.j_sub_I_quadratic
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Residues.normalizedDeriv_jInvariantFun

/-!
# `j'` vanishes to *first* order at the elliptic point `i`

The elliptic point `i` is a fixed point of `S : τ ↦ -1/τ`, so `E₆(i) = 0` and hence
`j'(i) = -2πi E₄(i)²E₆(i)/Δ(i) = 0`.  This file computes the derivative of `j'` at `i` and shows
that it is non-zero: `j'` has a *simple* zero at `i` (equivalently `j` has a double critical point
there).

The computation is the bookkeeping of the identity `j' = 2πi·D j` where `D = (2πi)⁻¹ d/dτ` is the
normalized derivative.  Since `j' ∘ ofComplex` is the (honest) complex derivative of
`j ∘ ofComplex`, its derivative at `i` is the second derivative of `j`.  Writing
`j'(τ) = -2πi E₄(τ)²E₆(τ)/Δ(τ)` and differentiating with the quotient rule, the only surviving
terms at `τ = i` are those containing a *derivative* of `E₆` (since `E₆(i) = 0` kills all others):

  `(j'∘ofComplex)'(i) = -2πi · E₄(i)² · (E₆∘ofComplex)'(i) / Δ(i)`.

Ramanujan's identity `D E₆ = (E₂E₆ - E₄²)/2` (`Work.Modular.ramanujan_E6`) gives
`(E₆∘ofComplex)'(i) = 2πi·D E₆(i) = -πi E₄(i)²`, whence

  `(j'∘ofComplex)'(i) = -2π² E₄(i)⁴/Δ(i) ≠ 0`,

because `E₄(i) ≠ 0` (from `1728 Δ(i) = E₄(i)³ - E₆(i)² = E₄(i)³`) and `Δ(i) ≠ 0`.

## Main result

* `Work.Asymptotics.deriv_jprime_ofComplex_I_ne_zero`
-/

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-- `ofComplex I = I`, so the complex point `i` is the elliptic point of `ℍ`. -/
private lemma ofComplex_I : UpperHalfPlane.ofComplex Complex.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_inj.mp
  rw [← UpperHalfPlane.coe_I, UpperHalfPlane.ofComplex_apply]

/-- `E₆(i) = 0`: `E₆` transforms by `z⁶` under `S`, and `S` fixes `i`. -/
private lemma E6Fun_I_eq_zero : Work.Kernels.E6Fun UpperHalfPlane.I = 0 := by
  have hS : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
    rw [inv_neg, Complex.inv_I]
    ring
  have h := Work.Residues.E6Fun_S_smul UpperHalfPlane.I
  rw [hS] at h
  have hI6 : (UpperHalfPlane.I : ℂ) ^ 6 = -1 := by
    rw [UpperHalfPlane.coe_I, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [hI6, neg_one_mul] at h
  have h2 : (2 : ℂ) * Work.Kernels.E6Fun UpperHalfPlane.I = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- `E₄(i) ≠ 0`, from `1728 Δ(i) = E₄(i)³ - E₆(i)² = E₄(i)³` and `Δ(i) ≠ 0`. -/
private lemma E4Fun_I_ne_zero : Work.Kernels.E4Fun UpperHalfPlane.I ≠ 0 := by
  intro h4
  have h := Work.Residues.KMinusClearTS.disc_eq UpperHalfPlane.I
  rw [E6Fun_I_eq_zero, h4] at h
  norm_num at h
  exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero UpperHalfPlane.I h

/-- **The derivative of `E₆` at the elliptic point.**  The dictionary
`deriv (f ∘ ofComplex) = 2πi · D f` between the honest complex derivative and the normalized
derivative `D`, together with Ramanujan's identity `D E₆ = (E₂E₆ - E₄²)/2` and `E₆(i) = 0`, gives
`(E₆∘ofComplex)'(i) = -πi E₄(i)² ≠ 0`. -/
private lemma deriv_E6Fun_comp_I :
    deriv (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z)) Complex.I
      = -(Real.pi : ℂ) * Complex.I * Work.Kernels.E4Fun UpperHalfPlane.I ^ 2 := by
  have hdic : deriv (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) (UpperHalfPlane.I : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) *
        Derivative.normalizedDerivOfComplex Work.Kernels.E6Fun UpperHalfPlane.I := by
    rw [Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [UpperHalfPlane.coe_I] at hdic
  rw [show (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z))
      = (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) from rfl, hdic]
  rw [show Derivative.normalizedDerivOfComplex Work.Kernels.E6Fun UpperHalfPlane.I
      = (Work.Kernels.E2Fun UpperHalfPlane.I * Work.Kernels.E6Fun UpperHalfPlane.I
          - Work.Kernels.E4Fun UpperHalfPlane.I ^ 2) / 2 from
    congr_fun Work.Modular.ramanujan_E6 UpperHalfPlane.I]
  rw [E6Fun_I_eq_zero]
  ring

/-- **`j'`, viewed as a holomorphic function of the coordinate, has non-zero derivative at `i`.**
This is the main computation: the quotient rule for `-2πi E₄²E₆/Δ`, evaluated at `i`. -/
private lemma hasDerivAt_jprime_comp_I :
    HasDerivAt (fun z : ℂ => Work.Residues.jprime (ofComplex z))
      ((-(2 * (Real.pi : ℂ) * Complex.I) * Work.Kernels.E4Fun (ofComplex Complex.I) ^ 2 *
        deriv (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z)) Complex.I) /
        Work.Kernels.DeltaFun (ofComplex Complex.I)) Complex.I := by
  have hE6zero : Work.Kernels.E6Fun UpperHalfPlane.I = 0 := E6Fun_I_eq_zero
  have hE6zero' : Work.Kernels.E6Fun (ofComplex Complex.I) = 0 := by
    rw [ofComplex_I]; exact hE6zero
  have hDne : Work.Kernels.DeltaFun (ofComplex Complex.I) ≠ 0 :=
    Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hE4diff : DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.E4Fun (ofComplex z)) Complex.I :=
    UpperHalfPlane.mdifferentiableAt_iff.mp ((ModularFormClass.holo ModularForm.E₄) UpperHalfPlane.I)
  have hE6diff : DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z)) Complex.I :=
    UpperHalfPlane.mdifferentiableAt_iff.mp ((ModularFormClass.holo ModularForm.E₆) UpperHalfPlane.I)
  have hDdiff : DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.DeltaFun (ofComplex z)) Complex.I :=
    UpperHalfPlane.mdifferentiableAt_iff.mp
      ((ModularFormClass.holo (CuspForm.discriminant :
        CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12)) UpperHalfPlane.I)
  have hfun : (((fun _ : ℂ => -(2 * (Real.pi : ℂ) * Complex.I)) *
        (fun z : ℂ => Work.Kernels.E4Fun (ofComplex z)) ^ 2 *
        fun z => Work.Kernels.E6Fun (ofComplex z)) /
      fun z => Work.Kernels.DeltaFun (ofComplex z))
      = (fun z : ℂ => Work.Residues.jprime (ofComplex z)) := by
    funext z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Work.Residues.jprime]
  have hE4 := hE4diff.hasDerivAt
  have hE6 := hE6diff.hasDerivAt
  have hD := hDdiff.hasDerivAt
  have hN := ((hasDerivAt_const (Complex.I) (-(2 * (Real.pi : ℂ) * Complex.I))).mul
    (hE4.pow 2)).mul hE6
  have hq := hN.div hD hDne
  rw [hfun] at hq
  refine hq.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, hE6zero', mul_zero, zero_mul, sub_zero]
  field_simp
  ring_nf

/-- **`j'` has a simple zero at the elliptic point `i`.**  Translating the non-vanishing of the
derivative of `j'` at `i` into the derivative of the map `a ↦ j'(i + a)`. -/
theorem deriv_jprime_ofComplex_I_ne_zero :
    deriv (fun a : ℂ => Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + a))) 0 ≠ 0 := by
  have hDne : Work.Kernels.DeltaFun (ofComplex Complex.I) ≠ 0 :=
    Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hE4ne : Work.Kernels.E4Fun UpperHalfPlane.I ≠ 0 := E4Fun_I_ne_zero
  have hE4ne' : Work.Kernels.E4Fun (ofComplex Complex.I) ≠ 0 := by
    rw [ofComplex_I]; exact hE4ne
  have he6ne : deriv (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z)) Complex.I ≠ 0 := by
    rw [deriv_E6Fun_comp_I]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · exact Complex.I_ne_zero
    · exact pow_ne_zero 2 hE4ne
  have hA0 : HasDerivAt (fun z : ℂ => Work.Residues.jprime (ofComplex z))
      ((-(2 * (Real.pi : ℂ) * Complex.I) * Work.Kernels.E4Fun (ofComplex Complex.I) ^ 2 *
        deriv (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z)) Complex.I) /
        Work.Kernels.DeltaFun (ofComplex Complex.I)) (Complex.I + 0) := by
    simpa using hasDerivAt_jprime_comp_I
  have hshift : HasDerivAt (fun a : ℂ => Complex.I + a) 1 0 :=
    (hasDerivAt_id (0 : ℂ)).const_add Complex.I
  have hcomp : HasDerivAt
      (fun a : ℂ => Work.Residues.jprime (ofComplex (Complex.I + a)))
      ((-(2 * (Real.pi : ℂ) * Complex.I) * Work.Kernels.E4Fun (ofComplex Complex.I) ^ 2 *
        deriv (fun z : ℂ => Work.Kernels.E6Fun (ofComplex z)) Complex.I) /
        Work.Kernels.DeltaFun (ofComplex Complex.I)) 0 := by
    have h := hA0.comp 0 hshift
    simpa [Function.comp_def, mul_one] using h
  rw [hcomp.deriv]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero))
    (pow_ne_zero 2 hE4ne')) he6ne) hDne

end

end Work.Asymptotics
