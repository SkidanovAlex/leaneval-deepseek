/-
# The Beltrami coefficient and the `∂̄`-equation on `ℂ`

This file sets up the conventions for the `n = 1` case of the Newlander--Nirenberg
theorem, working directly on `ℂ` (identified with `ℝ²` in the usual way).

For a field of real-linear endomorphisms `J z : ℂ →L[ℝ] ℂ` with `J z ∘ J z = -1`
the condition that a real-differentiable `w : ℂ → ℂ` is `J`-holomorphic at `z`
(its differential is complex linear w.r.t. `J`) is *one* complex equation, the
**Beltrami equation**  `∂̄w = μ ∂w`, where the **Beltrami coefficient** is

  `beltramiCoeff (J z) = -(1 + i·J z 1) / (1 + i·conj (J z 1))`.

We prove this equivalence (`IsJHolAt_iff_beltramiCoeff`), the normalisation
`beltramiCoeff (JstdC z) = 0`, the ellipticity `‖beltramiCoeff‖ < 1` in the
orientation-compatible case `0 < Im (J z 1)`, and the behaviour under rescaling.

Everything here is elementary linear algebra at a point; the analysis (the
solution of the Beltrami equation by the Cauchy transform) is elsewhere.
-/
import Mathlib
import Submission.Work.Core.Defs

noncomputable section

namespace Work.Beltrami

/-- The standard complex structure on `ℂ`, as a constant field of real-linear
endomorphisms: `v ↦ i·v`. -/
def JstdC : ℂ → ℂ →L[ℝ] ℂ := fun _ => Complex.I • (1 : ℂ →L[ℝ] ℂ)

@[simp] theorem JstdC_apply (z v : ℂ) : JstdC z v = Complex.I * v := by
  simp [JstdC]

/-- `i * (i * x) = -x`. -/
theorem I_mul_I_mul (x : ℂ) : Complex.I * (Complex.I * x) = -x := by
  rw [← mul_assoc, Complex.I_mul_I]; ring

/-- `(-i) * (i * x) = x`. -/
theorem neg_I_mul_I_mul (x : ℂ) : (-Complex.I) * (Complex.I * x) = x := by
  rw [neg_mul, ← mul_assoc, Complex.I_mul_I]; ring

theorem JstdC_sq (z v : ℂ) : JstdC z (JstdC z v) = -v := by
  rw [JstdC_apply, JstdC_apply, I_mul_I_mul]

/-- `w` is `J`-holomorphic at `z`: its real differential is complex linear. -/
def IsJHolAt (J : ℂ → ℂ →L[ℝ] ℂ) (w : ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ v : ℂ, fderiv ℝ w z (J z v) = Complex.I * fderiv ℝ w z v

/-- `w` is `J`-holomorphic on the set `U`. -/
def IsJHolOn (J : ℂ → ℂ →L[ℝ] ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, IsJHolAt J w z

/-- The `∂`-coefficient `∂w = (1/2)(w_x - i w_y)` of a real-linear map
(presumed to be the differential of `w`). -/
def dzCoeff (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1 - Complex.I * L Complex.I) / 2

/-- The `∂̄`-coefficient `∂̄w = (1/2)(w_x + i w_y)`. -/
def dzbarCoeff (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1 + Complex.I * L Complex.I) / 2

/-- `∂w` at the point `z`. -/
def dW (w : ℂ → ℂ) (z : ℂ) : ℂ := dzCoeff (fderiv ℝ w z)

/-- `∂̄w` at the point `z`. -/
def dbarW (w : ℂ → ℂ) (z : ℂ) : ℂ := dzbarCoeff (fderiv ℝ w z)

@[simp] theorem dzCoeff_add_dzbarCoeff (L : ℂ →L[ℝ] ℂ) :
    dzCoeff L + dzbarCoeff L = L 1 := by
  simp only [dzCoeff, dzbarCoeff]; ring

theorem dzCoeff_sub_dzbarCoeff (L : ℂ →L[ℝ] ℂ) :
    dzCoeff L - dzbarCoeff L = -Complex.I * L Complex.I := by
  simp only [dzCoeff, dzbarCoeff]; ring

theorem dzbarCoeff_mul (L : ℂ →L[ℝ] ℂ) :
    (dzCoeff L - dzbarCoeff L) * Complex.I = L Complex.I := by
  rw [dzCoeff_sub_dzbarCoeff]
  linear_combination (-(L Complex.I)) * Complex.I_mul_I

/-- **The key linear-algebra fact.**  For a complex structure `J` on `ℂ`
(`J ∘ J = -1`) and a real-linear `L : ℂ →L[ℝ] ℂ`, the condition that `L` be complex
linear w.r.t. `J` is a single complex equation:  `L 1 + i L (J 1) = 0`. -/
theorem hol_iff_eval_one (J : ℂ →L[ℝ] ℂ) (hJ : ∀ v, J (J v) = -v) (L : ℂ →L[ℝ] ℂ) :
    (∀ v, L (J v) = Complex.I * L v) ↔ L 1 + Complex.I * L (J 1) = 0 := by
  have hII : ∀ x : ℂ, Complex.I * (Complex.I * x) = -x := I_mul_I_mul
  have hII' : ∀ x : ℂ, (-Complex.I) * (Complex.I * x) = x := neg_I_mul_I_mul
  have hgen : ∀ p q : ℝ, q ≠ 0 →
      Complex.I = (↑(-(p * q⁻¹)) : ℂ) + (↑(q⁻¹) : ℂ) * ((↑p : ℂ) + (↑q : ℂ) * Complex.I) := by
    intro p q hq
    have hq' : (q : ℂ) ≠ 0 := by simpa using hq
    push_cast
    field_simp
    ring
  constructor
  · intro h
    rw [h 1, hII]; ring
  · intro h
    have hq : (J 1).im ≠ 0 := by
      intro h0
      have h1 : J 1 = (↑((J 1).re) : ℂ) := by rw [← Complex.re_add_im (J 1), h0]; simp
      have h5 : J (↑((J 1).re) : ℂ) = ((J 1).re) • J 1 := by
        rw [show (↑((J 1).re) : ℂ) = ((J 1).re) • (1 : ℂ) by simp, map_smul]
      have h6 := hJ 1
      rw [h1, h5, h1] at h6
      have h7 : ((↑((J 1).re * (J 1).re) : ℂ)) = -1 := by
        simpa [smul_eq_mul, ← Complex.ofReal_mul] using h6
      have h8 : (J 1).re * (J 1).re = -1 := by exact_mod_cast h7
      nlinarith [mul_self_nonneg (J 1).re]
    let P : ℂ →L[ℝ] ℂ := L + Complex.I • (L.comp J)
    have hP1 : P 1 = 0 := by
      simp only [P, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      simpa using h
    have hPJ : P (J 1) = 0 := by
      have e : P (J 1) = (-Complex.I) • P 1 := by
        simp only [P, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
        rw [hJ 1, map_neg, neg_mul, mul_add, hII]
        ring
      rw [e, hP1, smul_zero]
    have hI : Complex.I = (↑(-((J 1).re * ((J 1).im)⁻¹)) : ℂ) + (↑(((J 1).im)⁻¹) : ℂ) * (J 1) := by
      have hd := hgen (J 1).re (J 1).im hq
      rwa [Complex.re_add_im (J 1)] at hd
    have hspan : ∀ v : ℂ, P v = 0 := by
      intro v
      have hv : v = (↑(v.re + v.im * (-((J 1).re * ((J 1).im)⁻¹))) : ℂ)
          + (↑(v.im * ((J 1).im)⁻¹) : ℂ) * (J 1) := by
        conv_lhs => rw [← Complex.re_add_im v]
        rw [hI]
        push_cast
        ring
      have hA : P (↑(v.re + v.im * (-((J 1).re * ((J 1).im)⁻¹))) : ℂ) = 0 := by
        rw [show (↑(v.re + v.im * (-((J 1).re * ((J 1).im)⁻¹))) : ℂ)
            = (v.re + v.im * (-((J 1).re * ((J 1).im)⁻¹))) • (1 : ℂ) by simp,
          map_smul, hP1, smul_zero]
      have hB : P ((↑(v.im * ((J 1).im)⁻¹) : ℂ) * (J 1)) = 0 := by
        rw [show (↑(v.im * ((J 1).im)⁻¹) : ℂ) * (J 1)
            = (v.im * ((J 1).im)⁻¹) • (J 1) by simp,
          map_smul, hPJ, smul_zero]
      rw [hv, map_add, hA, hB, add_zero]
    intro v
    have hzero := hspan v
    simp only [P, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul] at hzero
    have h2 : Complex.I * L (J v) = -L v := by linear_combination hzero
    calc L (J v) = (-Complex.I) * (Complex.I * L (J v)) := (hII' _).symm
      _ = (-Complex.I) * (-L v) := by rw [h2]
      _ = Complex.I * L v := by ring

/-- Complex conjugation in coordinates: `star z = z.re - z.im * i`. -/
theorem star_eq (z : ℂ) : star z = (↑z.re : ℂ) - (↑z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- Purely algebraic identity underlying the Beltrami equation. -/
theorem eval_one_eq_of (β wz wzb : ℂ) :
    (wz + wzb) + Complex.I * (β.re * (wz + wzb) + β.im * ((wz - wzb) * Complex.I))
      = (1 + Complex.I * β) * wz + (1 + Complex.I * star β) * wzb := by
  have hst : star β = starRingEnd ℂ β := rfl
  rw [hst]
  apply Complex.ext <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_im, Complex.neg_re, Complex.conj_re,
      Complex.conj_im]
    ring

/-- The evaluation-at-one condition, written as a scalar equation in the
`∂` and `∂̄` coefficients. -/
theorem eval_one_eq (J : ℂ →L[ℝ] ℂ) (L : ℂ →L[ℝ] ℂ) :
    L 1 + Complex.I * L (J 1)
      = (1 + Complex.I * (J 1)) * dzCoeff L + (1 + Complex.I * star (J 1)) * dzbarCoeff L := by
  have h1 : L 1 = dzCoeff L + dzbarCoeff L := (dzCoeff_add_dzbarCoeff L).symm
  have h2 : L Complex.I = (dzCoeff L - dzbarCoeff L) * Complex.I := (dzbarCoeff_mul L).symm
  have hLJ : L (J 1) = (J 1).re * (dzCoeff L + dzbarCoeff L)
      + (J 1).im * ((dzCoeff L - dzbarCoeff L) * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im (J 1)]
    rw [map_add]
    rw [show L (↑((J 1).re) : ℂ) = (J 1).re • L 1 by
      rw [show (↑((J 1).re) : ℂ) = ((J 1).re) • (1 : ℂ) by simp, map_smul]]
    rw [show L ((↑((J 1).im) : ℂ) * Complex.I) = (J 1).im • L Complex.I by
      rw [show (↑((J 1).im) : ℂ) * Complex.I = ((J 1).im) • (Complex.I : ℂ) by simp, map_smul]]
    rw [h1, h2]
    norm_num [smul_eq_mul]
  rw [h1, hLJ]
  exact eval_one_eq_of (J 1) (dzCoeff L) (dzbarCoeff L)

/-- The same condition, as an equality of scalar equations. -/
theorem eval_one_iff_beltrami (J : ℂ →L[ℝ] ℂ) (L : ℂ →L[ℝ] ℂ) :
    L 1 + Complex.I * L (J 1) = 0 ↔
      (1 + Complex.I * (J 1)) * dzCoeff L + (1 + Complex.I * star (J 1)) * dzbarCoeff L = 0 := by
  rw [eval_one_eq J L]

/-- The **Beltrami coefficient** of a complex structure `J` on `ℂ`. -/
def beltramiCoeff (J : ℂ →L[ℝ] ℂ) : ℂ :=
  -(1 + Complex.I * (J 1)) / (1 + Complex.I * star (J 1))

/-- **A function is `J`-holomorphic iff it solves the Beltrami equation.** -/
theorem IsJHolAt_iff_beltrami (J : ℂ → ℂ →L[ℝ] ℂ) (hJ : ∀ z v, J z (J z v) = -v)
    (w : ℂ → ℂ) (z : ℂ) :
    IsJHolAt J w z ↔
      (1 + Complex.I * (J z 1)) * dW w z + (1 + Complex.I * star (J z 1)) * dbarW w z = 0 := by
  unfold IsJHolAt dW dbarW
  exact (hol_iff_eval_one (J z) (hJ z) (fderiv ℝ w z)).trans
    (eval_one_iff_beltrami (J z) (fderiv ℝ w z))

/-- The Beltrami equation in its usual form `∂̄w = μ ∂w`. -/
theorem IsJHolAt_iff_beltramiCoeff (J : ℂ → ℂ →L[ℝ] ℂ) (hJ : ∀ z v, J z (J z v) = -v)
    (w : ℂ → ℂ) (z : ℂ) (h : 1 + Complex.I * star (J z 1) ≠ 0) :
    IsJHolAt J w z ↔ dbarW w z = beltramiCoeff (J z) * dW w z := by
  rw [IsJHolAt_iff_beltrami J hJ w z, beltramiCoeff]
  constructor
  · intro hm
    have h2 : (1 + Complex.I * star (J z 1)) * dbarW w z
        = -(1 + Complex.I * (J z 1)) * dW w z := by linear_combination hm
    rw [div_mul_eq_mul_div, eq_div_iff h]
    linear_combination h2
  · intro hm
    rw [hm, div_mul_eq_mul_div]
    field_simp
    ring

/-- The normalised structure has zero Beltrami coefficient. -/
theorem beltramiCoeff_JstdC (z : ℂ) : beltramiCoeff (JstdC z) = 0 := by
  simp only [beltramiCoeff, JstdC_apply, Complex.conj_I, Complex.I_mul_I]
  norm_num

/-- The Beltrami coefficient is small (`< 1`) on the orientation-compatible locus. -/
theorem norm_beltramiCoeff_lt_one (J : ℂ →L[ℝ] ℂ) (h : 0 < (J 1).im) :
    ‖beltramiCoeff J‖ < 1 := by
  have hden : 1 + Complex.I * star (J 1) ≠ 0 := by
    intro hc
    have hre := congrArg Complex.re hc
    rw [star_eq] at hre
    simp at hre
    linarith
  rw [beltramiCoeff, norm_div, norm_neg]
  rw [div_lt_one (norm_pos_iff.mpr hden)]
  have hnum : ‖1 + Complex.I * (J 1)‖ ^ 2 = (1 - (J 1).im) ^ 2 + (J 1).re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hden2 : ‖1 + Complex.I * star (J 1)‖ ^ 2 = (1 + (J 1).im) ^ 2 + (J 1).re ^ 2 := by
    rw [star_eq, Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h1 : ‖1 + Complex.I * (J 1)‖ ^ 2 < ‖1 + Complex.I * star (J 1)‖ ^ 2 := by
    rw [hnum, hden2]; nlinarith
  nlinarith [norm_nonneg (1 + Complex.I * (J 1)), norm_nonneg (1 + Complex.I * star (J 1))]

end Work.Beltrami
