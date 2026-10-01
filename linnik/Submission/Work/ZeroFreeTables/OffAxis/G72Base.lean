import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Defs
import Submission.Work.ZeroFreeTables.tf72Fc_imag_re_nonneg

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables
open scoped BigOperators

/-! ## The closed form of `G72` and its real part

`G72 w = ∫₀² e^{-wy} g72 y dy` has the elementary closed form
`G72 w = A72 w + e^{-2w} · B72 w` with the rational functions
`A72 w = (1/30)(32/w - 80/w³ + 120/w⁴ - 120/w⁶)`, `B72 w = 4(1+w)²/w⁶`
(the antiderivative being `y ↦ e^{-wy}q_w(y)` for the degree-five polynomial `q_w`
solving `q_w' - w q_w = g72`).

Writing `w = -s + iσ` and taking real parts gives `Re G72 w` as a rational function of
`(s,σ)` (`RA72`, `RB72`, `RI72`) plus `e^{2s}`, `cos 2σ`, `sin 2σ`.  -/

/-- The non-exponential part `A(w)` of the closed form of `G72`. -/
def A72 (w : ℂ) : ℂ := ((1 : ℂ)/30)*(32/w - 80/w^3 + 120/w^4 - 120/w^6)

/-- The coefficient `B(w)` of the exponential part of the closed form of `G72`. -/
def B72 (w : ℂ) : ℂ := 4*(1+w)^2/w^6

/-- Real form of `Re (A72 (-s + iσ))`. -/
def RA72 (s σ : ℝ) : ℝ :=
  -16*s/(15*(s^2+σ^2)) - (8/3)*(3*s*σ^2 - s^3)/(s^2+σ^2)^3
    + 4*(s^4 - 6*s^2*σ^2 + σ^4)/(s^2+σ^2)^4
    - 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)/(s^2+σ^2)^6

/-- Real form of `Re (B72 (-s + iσ))`. -/
def RB72 (s σ : ℝ) : ℝ :=
  4*(((1-s)^2 - σ^2)*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)
      - (2*(1-s)*σ)*(6*s^5*σ - 20*s^3*σ^3 + 6*s*σ^5))/(s^2+σ^2)^6

/-- Real form of `Im (B72 (-s + iσ))`. -/
def RI72 (s σ : ℝ) : ℝ :=
  4*(((1-s)^2 - σ^2)*(6*s^5*σ - 20*s^3*σ^3 + 6*s*σ^5)
      + (2*(1-s)*σ)*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6))/(s^2+σ^2)^6

/-- The quantity bounded by HB (10.8) at `λ = 6/7` (scale-free form):
`Isub s σ = Re G72(-s+iσ) - 2 Re G72(iσ)`. -/
def Isub (s σ : ℝ) : ℝ :=
  (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re
    - 2 * (G72 ((σ : ℂ) * Complex.I)).re

/-! ## The auxiliary lemmas (proved in companion modules) -/

end Work.ZeroFreeTables.OffAxis

namespace Work.ZeroFreeTables.OffAxis



/-! ## Derivative helpers -/

/-- Derivative of a real degree-five polynomial. -/
lemma hasDerivAt_poly6 (c0 c1 c2 c3 c4 c5 t : ℝ) :
    HasDerivAt (fun s : ℝ => c0 + c1*s + c2*s^2 + c3*s^3 + c4*s^4 + c5*s^5)
      (c1 + c2*(2*t) + c3*(3*t^2) + c4*(4*t^3) + c5*(5*t^4)) t := by
  have h0 : HasDerivAt (fun _ : ℝ => c0) 0 t := hasDerivAt_const t c0
  have h1 : HasDerivAt (fun s : ℝ => c1*s) c1 t := by
    simpa using (hasDerivAt_id t).const_mul c1
  have h2 : HasDerivAt (fun s : ℝ => c2*s^2) (c2*(2*t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul c2
  have h3 : HasDerivAt (fun s : ℝ => c3*s^3) (c3*(3*t^2)) t := by
    simpa using (hasDerivAt_pow 3 t).const_mul c3
  have h4 : HasDerivAt (fun s : ℝ => c4*s^4) (c4*(4*t^3)) t := by
    simpa using (hasDerivAt_pow 4 t).const_mul c4
  have h5 : HasDerivAt (fun s : ℝ => c5*s^5) (c5*(5*t^4)) t := by
    simpa using (hasDerivAt_pow 5 t).const_mul c5
  have h := ((((h0.add h1).add h2).add h3).add h4).add h5
  exact h.congr_deriv (by ring)

/-- Derivative of a complex degree-five polynomial in a real variable. -/
lemma hasDerivAt_poly6C (c0 c1 c2 c3 c4 c5 : ℂ) (y : ℝ) :
    HasDerivAt (fun s : ℝ => c0 + c1*(s:ℂ) + c2*(s:ℂ)^2 + c3*(s:ℂ)^3 + c4*(s:ℂ)^4 + c5*(s:ℂ)^5)
      (c1 + c2*(2*(y:ℂ)) + c3*(3*(y:ℂ)^2) + c4*(4*(y:ℂ)^3) + c5*(5*(y:ℂ)^4)) y := by
  have h0 : HasDerivAt (fun _ : ℝ => c0) 0 y := hasDerivAt_const y c0
  have h1 : HasDerivAt (fun s : ℝ => c1*(s:ℂ)) c1 y := by
    simpa using ((hasDerivAt_id (y:ℂ)).comp_ofReal).const_mul c1
  have h2 : HasDerivAt (fun s : ℝ => c2*(s:ℂ)^2) (c2*(2*(y:ℂ))) y := by
    simpa using ((hasDerivAt_pow 2 (y:ℂ)).comp_ofReal).const_mul c2
  have h3 : HasDerivAt (fun s : ℝ => c3*(s:ℂ)^3) (c3*(3*(y:ℂ)^2)) y := by
    simpa using ((hasDerivAt_pow 3 (y:ℂ)).comp_ofReal).const_mul c3
  have h4 : HasDerivAt (fun s : ℝ => c4*(s:ℂ)^4) (c4*(4*(y:ℂ)^3)) y := by
    simpa using ((hasDerivAt_pow 4 (y:ℂ)).comp_ofReal).const_mul c4
  have h5 : HasDerivAt (fun s : ℝ => c5*(s:ℂ)^5) (c5*(5*(y:ℂ)^4)) y := by
    simpa using ((hasDerivAt_pow 5 (y:ℂ)).comp_ofReal).const_mul c5
  have h := ((((h0.add h1).add h2).add h3).add h4).add h5
  exact h.congr_deriv (by ring)

/-! ## The complex closed form of `G72` -/

/-- The antiderivative polynomial `q_w` (solving `q_w' - w q_w = g72`). -/
noncomputable def q72 (w : ℂ) (y : ℝ) : ℂ :=
  (4/w^6 - 4/w^4 + 8/(3*w^3) - 16/(15*w))
  + (4/w^5 - 4/w^3 + 8/(3*w^2)) * (y:ℂ)
  + (2/w^4 - 2/w^2 + 4/(3*w)) * (y:ℂ)^2
  + (2/(3*w^3) - 2/(3*w)) * (y:ℂ)^3
  + (1/(6*w^2)) * (y:ℂ)^4
  + (1/(30*w)) * (y:ℂ)^5

lemma hasDerivAt_exp_mul_poly6C (w c0 c1 c2 c3 c4 c5 : ℂ) (y : ℝ) :
    HasDerivAt
      (fun s : ℝ => Complex.exp (-(w*(s:ℂ)))
        * (c0 + c1*(s:ℂ) + c2*(s:ℂ)^2 + c3*(s:ℂ)^3 + c4*(s:ℂ)^4 + c5*(s:ℂ)^5))
      (Complex.exp (-(w*(y:ℂ)))
        * ((c1 + c2*(2*(y:ℂ)) + c3*(3*(y:ℂ)^2) + c4*(4*(y:ℂ)^3) + c5*(5*(y:ℂ)^4))
          - w*(c0 + c1*(y:ℂ) + c2*(y:ℂ)^2 + c3*(y:ℂ)^3 + c4*(y:ℂ)^4 + c5*(y:ℂ)^5))) y := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (-(w*(s:ℂ))))
      (Complex.exp (-(w*(y:ℂ))) * (-w)) y := by
    have hid : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) y :=
      (hasDerivAt_id (y:ℂ)).comp_ofReal
    have h2 : HasDerivAt (fun s : ℝ => w*(s:ℂ)) w y := by
      simpa using hid.const_mul w
    have h3 : HasDerivAt (fun s : ℝ => -(w*(s:ℂ))) (-w) y := by
      have h := h2.neg
      have hfun : (fun s : ℝ => -(w*(s:ℂ))) = -(fun s : ℝ => w*(s:ℂ)) := rfl
      rw [hfun]; exact h
    have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-(w*(s:ℂ))))
        (Complex.exp (-(w*(y:ℂ))) * (-w)) y :=
      (Complex.hasDerivAt_exp (-(w*(y:ℂ)))).comp y h3
    exact h4
  have hp := hasDerivAt_poly6C c0 c1 c2 c3 c4 c5 y
  have hm := he.mul hp
  exact hm.congr_deriv (by ring)

/-- **The antiderivative of `e^{-wy} g72 y`.** -/
lemma hasDerivAt_exp_q72 (w : ℂ) (hw : w ≠ 0) (y : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(w*(s:ℂ))) * q72 w s)
      (Complex.exp (-(w*(y:ℂ))) * ((g72 y : ℝ) : ℂ)) y := by
  have h := hasDerivAt_exp_mul_poly6C w
    (4/w^6 - 4/w^4 + 8/(3*w^3) - 16/(15*w))
    (4/w^5 - 4/w^3 + 8/(3*w^2))
    (2/w^4 - 2/w^2 + 4/(3*w))
    (2/(3*w^3) - 2/(3*w))
    (1/(6*w^2)) (1/(30*w)) y
  refine h.congr_deriv ?_
  have hg : ((g72 y : ℝ) : ℂ) = (1/30)*(((2:ℂ) - (y:ℂ))^3 * (4 + 6*(y:ℂ) + (y:ℂ)^2)) := by
    simp only [g72]; push_cast; ring
  rw [hg]
  push_cast
  field_simp
  ring

lemma q72_at_two (w : ℂ) (hw : w ≠ 0) : q72 w 2 = B72 w := by
  simp only [q72, B72]
  push_cast
  field_simp
  ring

lemma q72_at_zero (w : ℂ) (hw : w ≠ 0) : q72 w 0 = -A72 w := by
  simp only [q72, A72]
  push_cast
  field_simp
  ring

/-- **Closed form of the Laplace transform `G72`.** -/
theorem G72_eq_closed {w : ℂ} (hw : w ≠ 0) :
    G72 w = A72 w + Complex.exp (-2*w) * B72 w := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(w*(s:ℂ))) * q72 w s)
      (Complex.exp (-(w*(y:ℂ))) * ((g72 y : ℝ) : ℂ)) y := fun y => hasDerivAt_exp_q72 w hw y
  have hcont : ContinuousOn (fun y : ℝ => Complex.exp (-(w*(y:ℂ))) * ((g72 y : ℝ):ℂ))
      (Set.Icc 0 2) := by
    apply Continuous.continuousOn
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hint : IntervalIntegrable (fun y : ℝ => Complex.exp (-(w*(y:ℂ))) * ((g72 y : ℝ):ℂ))
      MeasureTheory.volume (0:ℝ) 2 := hcont.intervalIntegrable_of_Icc (by norm_num)
  have hFTC : (∫ y in (0:ℝ)..2, Complex.exp (-(w*(y:ℂ))) * ((g72 y : ℝ) : ℂ))
      = Complex.exp (-(w*((2:ℝ):ℂ))) * q72 w 2 - Complex.exp (-(w*((0:ℝ):ℂ))) * q72 w 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  rw [G72, hFTC, q72_at_two w hw, q72_at_zero w hw]
  have h0 : Complex.exp (-(w*((0:ℝ):ℂ))) = 1 := by simp
  have h2 : Complex.exp (-(w*((2:ℝ):ℂ))) = Complex.exp (-2*w) := by
    congr 1; push_cast; ring
  rw [h0, h2]
  ring


/-! ## The real-integral representation of `Re G72` -/

/-- **`Re G72` as a real interval integral.** -/
theorem G72_re_eq_integral (z : ℂ) :
    (G72 z).re = ∫ y in (0:ℝ)..2, Real.exp (-(z.re * y)) * Real.cos (z.im * y) * g72 y := by
  have hpt : ∀ y : ℝ, (Complex.exp (-(z * (y:ℂ))) * ((g72 y : ℝ):ℂ)).re
      = Real.exp (-(z.re * y)) * Real.cos (z.im * y) * g72 y := by
    intro y
    have h1 : -(z * (y:ℂ)) = ((-(z.re*y) : ℝ) : ℂ) + ((-(z.im*y) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [h1, Complex.exp_add]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_re, Complex.exp_ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, mul_zero, sub_zero, zero_mul]
  have hcont : ContinuousOn (fun y : ℝ => Complex.exp (-(z * (y:ℂ))) * ((g72 y:ℝ):ℂ))
      (Set.Icc 0 2) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact Complex.continuous_ofReal.comp_continuousOn (by unfold g72; fun_prop)
  have hint : IntervalIntegrable (fun y : ℝ => Complex.exp (-(z * (y:ℂ))) * ((g72 y:ℝ):ℂ))
      MeasureTheory.volume (0:ℝ) 2 := hcont.intervalIntegrable_of_Icc (by norm_num)
  rw [G72]
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint]
  exact intervalIntegral.integral_congr (fun y _ => hpt y)

/-- **Isub as a real interval integral.** -/
theorem Isub_eq_integral (s σ : ℝ) :
    Isub s σ = ∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y := by
  have h1 : (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I).re = -s := by simp
    have i1 : (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I).im = σ := by simp
    rw [e1, i1]
    simp
  have h2 : (G72 ((σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((σ : ℂ) * Complex.I)).re = 0 := by simp
    have i1 : (((σ : ℂ) * Complex.I)).im = σ := by simp
    rw [e1, i1]
    simp
  rw [Isub, h1, h2]
  have hint1 : IntervalIntegrable (fun y : ℝ => Real.exp (s*y) * Real.cos (σ*y) * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hint2 : IntervalIntegrable (fun y : ℝ => 2 * (Real.cos (σ*y) * g72 y))
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1 hint2]
  apply intervalIntegral.integral_congr
  intro y _
  ring

/-! ## The real-part closed form of `G72`: explicit antiderivative

With `u = -s+iσ` and `ρ = s²+σ²`, the antiderivative polynomial `q_u` (see `q72`) has
`q_u(y) = q₀(s,σ,y) + i q₁(s,σ,y)` with the explicit real polynomials `Qp0`, `Qp1` below;
`q₀' + s q₀ + σ q₁ = g72` and `q₁' + s q₁ - σ q₀ = 0`, hence
`d/dy [e^{sy}(cos(σy) q₀ + sin(σy) q₁)] = e^{sy} cos(σy) g72 y`, and integrating from `0` to `2`
gives `Re G72(-s+iσ) = e^{2s}(cos 2σ · q₀(2) + sin 2σ · q₁(2)) - q₀(0)`
with `q₀(2) = RB72`, `q₁(2) = RI72`, `q₀(0) = -RA72`. -/

/-- Real part of the `y^0` coefficient of the antiderivative polynomial. -/
noncomputable def q0a (s σ : ℝ) : ℝ :=
  4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)/(s^2+σ^2)^6
    - 4*(s^4 - 6*s^2*σ^2 + σ^4)/(s^2+σ^2)^4
    + (8/3)*(3*s*σ^2 - s^3)/(s^2+σ^2)^3 + (16/15)*s/(s^2+σ^2)
noncomputable def q0b (s σ : ℝ) : ℝ :=
  -4*(s^5 - 10*s^3*σ^2 + 5*s*σ^4)/(s^2+σ^2)^5 - 4*(3*s*σ^2 - s^3)/(s^2+σ^2)^3
    + (8/3)*(s^2 - σ^2)/(s^2+σ^2)^2
noncomputable def q0c (s σ : ℝ) : ℝ :=
  2*(s^4 - 6*s^2*σ^2 + σ^4)/(s^2+σ^2)^4 - 2*(s^2 - σ^2)/(s^2+σ^2)^2 - (4/3)*s/(s^2+σ^2)
noncomputable def q0d (s σ : ℝ) : ℝ :=
  (2/3)*(3*s*σ^2 - s^3)/(s^2+σ^2)^3 + (2/3)*s/(s^2+σ^2)
noncomputable def q0e (s σ : ℝ) : ℝ := (s^2 - σ^2)/(6*(s^2+σ^2)^2)
noncomputable def q0f (s σ : ℝ) : ℝ := -s/(30*(s^2+σ^2))

noncomputable def q1a (s σ : ℝ) : ℝ :=
  4*(6*s^5*σ - 20*s^3*σ^3 + 6*s*σ^5)/(s^2+σ^2)^6
    - 4*(4*s^3*σ - 4*s*σ^3)/(s^2+σ^2)^4
    + (8/3)*(σ^3 - 3*s^2*σ)/(s^2+σ^2)^3 + (16/15)*σ/(s^2+σ^2)
noncomputable def q1b (s σ : ℝ) : ℝ :=
  -4*(5*s^4*σ - 10*s^2*σ^3 + σ^5)/(s^2+σ^2)^5 + 4*(3*s^2*σ - σ^3)/(s^2+σ^2)^3
    + (8/3)*(2*s*σ)/(s^2+σ^2)^2
noncomputable def q1c (s σ : ℝ) : ℝ :=
  2*(4*s^3*σ - 4*s*σ^3)/(s^2+σ^2)^4 - 2*(2*s*σ)/(s^2+σ^2)^2 - (4/3)*σ/(s^2+σ^2)
noncomputable def q1d (s σ : ℝ) : ℝ :=
  -(2/3)*(3*s^2*σ - σ^3)/(s^2+σ^2)^3 + (2/3)*σ/(s^2+σ^2)
noncomputable def q1e (s σ : ℝ) : ℝ := s*σ/(3*(s^2+σ^2)^2)
noncomputable def q1f (s σ : ℝ) : ℝ := -σ/(30*(s^2+σ^2))

/-- The real part of the antiderivative polynomial. -/
noncomputable def Qp0 (s σ y : ℝ) : ℝ :=
  q0a s σ + q0b s σ*y + q0c s σ*y^2 + q0d s σ*y^3 + q0e s σ*y^4 + q0f s σ*y^5

/-- The imaginary part of the antiderivative polynomial. -/
noncomputable def Qp1 (s σ y : ℝ) : ℝ :=
  q1a s σ + q1b s σ*y + q1c s σ*y^2 + q1d s σ*y^3 + q1e s σ*y^4 + q1f s σ*y^5

/-- Derivative of a real polynomial (non-numeric coefficients). -/
lemma hasDerivAt_poly6' (a0 a1 a2 a3 a4 a5 y : ℝ) :
    HasDerivAt (fun z : ℝ => a0 + a1*z + a2*z^2 + a3*z^3 + a4*z^4 + a5*z^5)
      (a1 + a2*(2*y) + a3*(3*y^2) + a4*(4*y^3) + a5*(5*y^4)) y :=
  hasDerivAt_poly6 a0 a1 a2 a3 a4 a5 y

lemma deriv_Qp0 (s σ y : ℝ) :
    HasDerivAt (fun y : ℝ => Qp0 s σ y)
      (q0b s σ + q0c s σ*(2*y) + q0d s σ*(3*y^2) + q0e s σ*(4*y^3) + q0f s σ*(5*y^4)) y := by
  have h := hasDerivAt_poly6 (q0a s σ) (q0b s σ) (q0c s σ) (q0d s σ) (q0e s σ) (q0f s σ) y
  exact h

lemma deriv_Qp1 (s σ y : ℝ) :
    HasDerivAt (fun y : ℝ => Qp1 s σ y)
      (q1b s σ + q1c s σ*(2*y) + q1d s σ*(3*y^2) + q1e s σ*(4*y^3) + q1f s σ*(5*y^4)) y := by
  have h := hasDerivAt_poly6 (q1a s σ) (q1b s σ) (q1c s σ) (q1d s σ) (q1e s σ) (q1f s σ) y
  exact h

/-- The two first-order identities satisfied by `Qp0`, `Qp1`. -/
lemma Qp_identities (s σ y : ℝ) (hρ : s^2 + σ^2 ≠ 0) :
    (q0b s σ + q0c s σ*(2*y) + q0d s σ*(3*y^2) + q0e s σ*(4*y^3) + q0f s σ*(5*y^4))
        + s*Qp0 s σ y + σ*Qp1 s σ y = g72 y
      ∧ (q1b s σ + q1c s σ*(2*y) + q1d s σ*(3*y^2) + q1e s σ*(4*y^3) + q1f s σ*(5*y^4))
        + s*Qp1 s σ y - σ*Qp0 s σ y = 0 := by
  have hg : g72 y = (1/30)*(32 - 40*y^2 + 20*y^3 - y^5) := by
    simp only [Work.ZeroFreeTables.g72]; ring
  rw [hg]
  constructor <;>
    simp only [Qp0, Qp1, q0a, q0b, q0c, q0d, q0e, q0f, q1a, q1b, q1c, q1d, q1e, q1f] <;>
    field_simp <;> ring

/-- The value identities: `q₀(0) = -RA72`, `q₀(2) = RB72`, `q₁(2) = RI72`. -/
lemma Qp_values (s σ : ℝ) (hρ : s^2 + σ^2 ≠ 0) :
    Qp0 s σ 0 = -RA72 s σ ∧ Qp0 s σ 2 = RB72 s σ ∧ Qp1 s σ 2 = RI72 s σ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Qp0, Qp1, RA72, RB72, RI72, q0a, q0b, q0c, q0d, q0e, q0f,
      q1a, q1b, q1c, q1d, q1e, q1f] <;>
    field_simp <;> ring

/-- Generic derivative of `e^{sy}(cos(σy) q₀(y) + sin(σy) q₁(y))`. -/
lemma deriv_exp_cos_sin (s σ q0' q1' y : ℝ) {q0 q1 : ℝ → ℝ}
    (h0 : HasDerivAt q0 q0' y) (h1 : HasDerivAt q1 q1' y) :
    HasDerivAt (fun z : ℝ => Real.exp (s*z)*(Real.cos (σ*z)*q0 z + Real.sin (σ*z)*q1 z))
      (Real.exp (s*y) * ((q0' + s*q0 y + σ*q1 y)*Real.cos (σ*y)
        + (q1' + s*q1 y - σ*q0 y)*Real.sin (σ*y))) y := by
  have he : HasDerivAt (fun z : ℝ => Real.exp (s*z)) (Real.exp (s*y)*s) y := by
    have h : HasDerivAt (fun z : ℝ => s*z) s y := by
      simpa using (hasDerivAt_id y).const_mul s
    exact h.exp
  have hc : HasDerivAt (fun z : ℝ => Real.cos (σ*z)) (-(Real.sin (σ*y)*σ)) y := by
    have h : HasDerivAt (fun z : ℝ => σ*z) σ y := by
      simpa using (hasDerivAt_id y).const_mul σ
    simpa only [neg_mul] using h.cos
  have hs : HasDerivAt (fun z : ℝ => Real.sin (σ*z)) (Real.cos (σ*y)*σ) y := by
    have h : HasDerivAt (fun z : ℝ => σ*z) σ y := by
      simpa using (hasDerivAt_id y).const_mul σ
    exact h.sin
  have h := he.mul ((hc.mul h0).add (hs.mul h1))
  refine h.congr_deriv ?_
  simp
  ring

/-- The antiderivative of `e^{sy} cos(σy) g72 y`. -/
lemma hasDerivAt_antideriv (s σ : ℝ) (hρ : s^2 + σ^2 ≠ 0) (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.exp (s*z)*(Real.cos (σ*z)*Qp0 s σ z + Real.sin (σ*z)*Qp1 s σ z))
      (Real.exp (s*y) * Real.cos (σ*y) * g72 y) y := by
  have h := deriv_exp_cos_sin s σ
    (q0b s σ + q0c s σ*(2*y) + q0d s σ*(3*y^2) + q0e s σ*(4*y^3) + q0f s σ*(5*y^4))
    (q1b s σ + q1c s σ*(2*y) + q1d s σ*(3*y^2) + q1e s σ*(4*y^3) + q1f s σ*(5*y^4))
    y (deriv_Qp0 s σ y) (deriv_Qp1 s σ y)
  obtain ⟨hid0, hid1⟩ := Qp_identities s σ y hρ
  refine h.congr_deriv ?_
  rw [hid0, hid1]
  ring

/-/-- **The real-part closed form of G72 at w = -s+iσ.** -/
theorem G72ReClosed0 {s σ : ℝ} (hρ : s^2 + σ^2 ≠ 0) :
    (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re
      = RA72 s σ
        + Real.exp (2*s) * (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ) := by
  have h1 : (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I).re = -s := by simp
    have i1 : (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I).im = σ := by simp
    rw [e1, i1]
    ring_nf
  rw [h1]
  have hcont : ContinuousOn (fun z : ℝ =>
      Real.exp (s*z)*(Real.cos (σ*z)*Qp0 s σ z + Real.sin (σ*z)*Qp1 s σ z)) (Set.Icc 0 2) := by
    apply Continuous.continuousOn
    simp only [Qp0, Qp1, q0a, q0b, q0c, q0d, q0e, q0f, q1a, q1b, q1c, q1d, q1e, q1f]
    fun_prop
  have hint : IntervalIntegrable (fun z : ℝ => Real.exp (s*z) * Real.cos (σ*z) * g72 z)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_antideriv s σ hρ y) hint
  obtain ⟨hv0, hv1, hv2⟩ := Qp_values s σ hρ
  rw [hFTC, hv0, hv1, hv2]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, Real.exp_zero, zero_mul, zero_add]
  ring_nf


/-! ## Elementary integral evaluations -/

/-- `g72` is non-negative on `[0,2]`. -/
lemma g72_nonneg {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) : 0 ≤ g72 y := by
  simp only [Work.ZeroFreeTables.g72]
  have h1 : 0 ≤ 2 - y := by linarith
  have h2 : 0 ≤ 4 + 6*y + y^2 := by nlinarith [hy, sq_nonneg (y+3)]
  positivity

/-- `∫₀² y g72 y dy = 16/35`. -/
lemma integral_y_g72 : ∫ y in (0:ℝ)..2, y * g72 y = 16/35 := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (1/30)*(16*z^2 - 10*z^4 + 4*z^5 - z^7/7))
      (y * g72 y) y := by
    intro y
    have h2 : HasDerivAt (fun z : ℝ => 16*z^2) (16*(2*y)) y := by
      simpa using (hasDerivAt_pow 2 y).const_mul (16:ℝ)
    have h4 : HasDerivAt (fun z : ℝ => 10*z^4) (10*(4*y^3)) y := by
      simpa using (hasDerivAt_pow 4 y).const_mul (10:ℝ)
    have h5 : HasDerivAt (fun z : ℝ => 4*z^5) (4*(5*y^4)) y := by
      simpa using (hasDerivAt_pow 5 y).const_mul (4:ℝ)
    have h7 : HasDerivAt (fun z : ℝ => z^7/7) (7*y^6/7) y := (hasDerivAt_pow 7 y).div_const 7
    have hsum := (((h2.sub h4).add h5).sub h7).const_mul (1/30)
    refine hsum.congr_deriv ?_
    simp only [Work.ZeroFreeTables.g72]
    ring
  have hint : IntervalIntegrable (fun y : ℝ => y * g72 y) MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  norm_num

/-- `∫₀² g72 y dy = 8/9`. -/
lemma integral_g72 : ∫ y in (0:ℝ)..2, g72 y = 8/9 := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (1/30)*(32*z - (40/3)*z^3 + 5*z^4 - z^6/6))
      (g72 y) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => 32*z) 32 y := by
      simpa using (hasDerivAt_id y).const_mul (32:ℝ)
    have h2 : HasDerivAt (fun z : ℝ => (40/3)*z^3) ((40/3)*(3*y^2)) y := by
      simpa using (hasDerivAt_pow 3 y).const_mul (40/3)
    have h3 : HasDerivAt (fun z : ℝ => 5*z^4) (5*(4*y^3)) y := by
      simpa using (hasDerivAt_pow 4 y).const_mul (5:ℝ)
    have h4 : HasDerivAt (fun z : ℝ => z^6/6) (6*y^5/6) y := (hasDerivAt_pow 6 y).div_const 6
    have h := (((h1.sub h2).add h3).sub h4).const_mul (1/30)
    refine h.congr_deriv ?_
    simp only [Work.ZeroFreeTables.g72]
    ring
  have hint : IntervalIntegrable (fun y : ℝ => g72 y) MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  norm_num

/-- `∫₀² y e^y g72 y dy = 16/15`. -/
lemma integral_y_exp_g72 : ∫ y in (0:ℝ)..2, y * Real.exp y * g72 y = 16/15 := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => Real.exp z * (-z^6 + 6*z^5 - 10*z^4 + 32*z - 32))
      (30 * (y * Real.exp y * g72 y)) y := by
    intro y
    have h2 : HasDerivAt (fun z : ℝ => -z^6 + 6*z^5 - 10*z^4 + 32*z - 32)
        (-6*y^5 + 30*y^4 - 40*y^3 + 32) y := by
      have h1 : HasDerivAt (fun z : ℝ => -(z^6)) (-(6*y^5)) y := (hasDerivAt_pow 6 y).neg
      have h2' : HasDerivAt (fun z : ℝ => 6*z^5) (6*(5*y^4)) y := (hasDerivAt_pow 5 y).const_mul 6
      have h3 : HasDerivAt (fun z : ℝ => -(10*z^4)) (-(10*(4*y^3))) y :=
        ((hasDerivAt_pow 4 y).const_mul 10).neg
      have h4 : HasDerivAt (fun z : ℝ => 32*z) 32 y := by
        simpa using (hasDerivAt_id y).const_mul (32:ℝ)
      have h5 : HasDerivAt (fun _ : ℝ => (-32:ℝ)) 0 y := hasDerivAt_const y _
      have h := ((((h1.add h2').add h3).add h4).add h5)
      refine h.congr_deriv ?_
      ring
    have hm := (Real.hasDerivAt_exp y).mul h2
    refine hm.congr_deriv ?_
    simp only [Work.ZeroFreeTables.g72]
    ring
  have hint : IntervalIntegrable (fun y : ℝ => 30 * (y * Real.exp y * g72 y))
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint
  rw [intervalIntegral.integral_const_mul] at h
  have h2 : Real.exp (2:ℝ) * (-(2:ℝ)^6 + 6*2^5 - 10*2^4 + 32*2 - 32)
      - Real.exp (0:ℝ) * (-(0:ℝ)^6 + 6*0^5 - 10*0^4 + 32*0 - 32) = 32 := by
    norm_num
  rw [h2] at h
  linarith

/-! ## Lipschitz bounds for `Isub` -/

/-- `e^{ty} - e^{sy} ≤ (t-s) y e^{ty}` for `0 ≤ s ≤ t`, `0 ≤ y`. -/
lemma exp_sub_exp_le (s t y : ℝ) (hst : s ≤ t) (hy : 0 ≤ y) :
    Real.exp (t*y) - Real.exp (s*y) ≤ (t-s)*y*Real.exp (t*y) := by
  have hkey : Real.exp (t*y) - Real.exp (s*y) = Real.exp (s*y) * (Real.exp ((t-s)*y) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [hkey]
  have hpos : (0:ℝ) < Real.exp ((t-s)*y) := Real.exp_pos _
  have h2 : Real.exp ((t-s)*y) - 1 ≤ (t-s)*y*Real.exp ((t-s)*y) := by
    have h := Real.add_one_le_exp (-((t-s)*y))
    have h3 : Real.exp (-((t-s)*y)) = (Real.exp ((t-s)*y))⁻¹ := Real.exp_neg _
    rw [h3] at h
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    rw [mul_inv_cancel₀ (ne_of_gt hpos)] at hm
    nlinarith [hm]
  have hfin : Real.exp (s*y) * (Real.exp ((t-s)*y) - 1)
      ≤ Real.exp (s*y) * ((t-s)*y*Real.exp ((t-s)*y)) :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
  have heq : Real.exp (s*y) * Real.exp ((t-s)*y) = Real.exp (t*y) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (s*y) * (Real.exp ((t-s)*y) - 1)
      ≤ Real.exp (s*y) * ((t-s)*y*Real.exp ((t-s)*y)) := hfin
    _ = (t-s)*y*Real.exp (t*y) := by rw [← heq]; ring

/-- `|e^{ty} - e^{sy}| ≤ |t-s| y e^y` for `s,t ∈ [0,1]`, `0 ≤ y`. -/
lemma abs_exp_sub_exp_le (s t y : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hs1 : s ≤ 1) (ht1 : t ≤ 1)
    (hy : 0 ≤ y) : |Real.exp (t*y) - Real.exp (s*y)| ≤ (|t-s|) * y * Real.exp y := by
  rcases le_total s t with h | h
  · have h1 := exp_sub_exp_le s t y h hy
    have h2 : Real.exp (t*y) ≤ Real.exp y := Real.exp_le_exp.mpr (by nlinarith)
    have h3 : Real.exp (s*y) ≤ Real.exp (t*y) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (by linarith : 0 ≤ Real.exp (t*y) - Real.exp (s*y))]
    calc Real.exp (t*y) - Real.exp (s*y) ≤ (t-s)*y*Real.exp (t*y) := h1
      _ ≤ (t-s)*y*Real.exp y := mul_le_mul_of_nonneg_left h2 (by positivity)
  · have h1 := exp_sub_exp_le t s y h hy
    have h2 : Real.exp (s*y) ≤ Real.exp y := Real.exp_le_exp.mpr (by nlinarith)
    have h3 : Real.exp (t*y) ≤ Real.exp (s*y) := Real.exp_le_exp.mpr (by nlinarith)
    have hsub : Real.exp (t*y) - Real.exp (s*y) ≤ 0 := by linarith
    rw [abs_of_nonpos hsub, abs_of_nonpos (sub_nonpos.mpr h)]
    simp only [neg_sub]
    calc Real.exp (s*y) - Real.exp (t*y) ≤ (s-t)*y*Real.exp (s*y) := h1
      _ ≤ (s-t)*y*Real.exp y := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **`Isub` is `16/15`-Lipschitz in `s`** on `[0,1]`. -/
theorem abs_Isub_sub_le_s (s t σ : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hs1 : s ≤ 1) (ht1 : t ≤ 1) :
    |Isub s σ - Isub t σ| ≤ (16/15) * |s - t| := by
  rw [Isub_eq_integral, Isub_eq_integral]
  set F : ℝ → ℝ := fun y => (Real.exp (s*y) - Real.exp (t*y)) * Real.cos (σ*y) * g72 y with hF
  have hkey : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y)
      - (∫ y in (0:ℝ)..2, (Real.exp (t*y) - 2) * Real.cos (σ*y) * g72 y)
      = ∫ y in (0:ℝ)..2, F y := by
    have hint1 : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    have hint2 : IntervalIntegrable (fun y : ℝ => (Real.exp (t*y) - 2) * Real.cos (σ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    rw [← intervalIntegral.integral_sub hint1 hint2]
    apply intervalIntegral.integral_congr
    intro y _
    simp only [hF]
    ring
  rw [hkey]
  have hnorm : |∫ y in (0:ℝ)..2, F y| ≤ ∫ y in (0:ℝ)..2, |F y| := by
    simpa [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
        (a := (0:ℝ)) (b := 2) (f := F)
  have hmono : (∫ y in (0:ℝ)..2, |F y|)
      ≤ ∫ y in (0:ℝ)..2, |s-t| * (y * Real.exp y * g72 y) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      simp only [hF, Work.ZeroFreeTables.g72]
      fun_prop
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    · intro y hy
      have hy0 : 0 ≤ y := hy.1
      have hg := g72_nonneg hy0 hy.2
      have h1 : |Real.exp (s*y) - Real.exp (t*y)| ≤ (|s-t|) * y * Real.exp y := by
        have hh := abs_exp_sub_exp_le s t y hs ht hs1 ht1 hy0
        rw [abs_sub_comm (Real.exp (t*y)) (Real.exp (s*y)), abs_sub_comm t s] at hh
        exact hh
      have h2 : |Real.cos (σ*y)| ≤ 1 := Real.abs_cos_le_one _
      simp only [hF]
      rw [abs_mul, abs_mul, abs_of_nonneg hg]
      calc |Real.exp (s*y) - Real.exp (t*y)| * |Real.cos (σ*y)| * g72 y
          ≤ ((|s-t|) * y * Real.exp y) * 1 * g72 y := by
            apply mul_le_mul_of_nonneg_right _ hg
            exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (|s-t|) * (y * Real.exp y * g72 y) := by ring
  have hval : (∫ y in (0:ℝ)..2, (|s-t|) * (y * Real.exp y * g72 y)) = (|s-t|) * (16/15) := by
    rw [intervalIntegral.integral_const_mul, integral_y_exp_g72]
  calc |∫ y in (0:ℝ)..2, F y| ≤ ∫ y in (0:ℝ)..2, |F y| := hnorm
    _ ≤ ∫ y in (0:ℝ)..2, (|s-t|) * (y * Real.exp y * g72 y) := hmono
    _ = (16/15) * |s - t| := by rw [hval]; ring

/-! ## Non-negativity on the imaginary axis -/

/-- **`Re G72(iσ) ≥ 0`.** -/
theorem G72ImagNonneg (σ : ℝ) : 0 ≤ (G72 ((σ : ℂ) * Complex.I)).re := by
  have h1 : (G72 ((σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((σ : ℂ) * Complex.I)).re = 0 := by simp
    have i1 : (((σ : ℂ) * Complex.I)).im = σ := by simp
    rw [e1, i1]
    simp
  have hg : (∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
      = (1/30) * ∫ y in (0:ℝ)..2,
          Real.cos (σ*y) * (32 - 40*y^2 + 20*y^3 - y^5) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    simp only [Work.ZeroFreeTables.g72]
    ring
  rw [h1, hg]
  have hpoly : (∫ y in (0:ℝ)..2, (32 - 40*y^2 + 20*y^3 - y^5)) = 80/3 := by
    have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => 32*z - (40/3)*z^3 + 5*z^4 - z^6/6)
        (32 - 40*y^2 + 20*y^3 - y^5) y := by
      intro y
      have h1 : HasDerivAt (fun z : ℝ => 32*z) 32 y := by
        simpa using (hasDerivAt_id y).const_mul (32:ℝ)
      have h2 : HasDerivAt (fun z : ℝ => (40/3)*z^3) ((40/3)*(3*y^2)) y := by
        simpa using (hasDerivAt_pow 3 y).const_mul (40/3)
      have h3 : HasDerivAt (fun z : ℝ => 5*z^4) (5*(4*y^3)) y := by
        simpa using (hasDerivAt_pow 4 y).const_mul (5:ℝ)
      have h4 : HasDerivAt (fun z : ℝ => z^6/6) (6*y^5/6) y := (hasDerivAt_pow 6 y).div_const 6
      have h := (((h1.sub h2).add h3).sub h4)
      refine h.congr_deriv ?_
      ring
    have hint : IntervalIntegrable (fun y : ℝ => 32 - 40*y^2 + 20*y^3 - y^5)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
    norm_num
  by_cases hσ : σ = 0
  · subst hσ
    have h2 : (∫ y in (0:ℝ)..2, Real.cos (0*y) * (32 - 40*y^2 + 20*y^3 - y^5))
        = ∫ y in (0:ℝ)..2, (32 - 40*y^2 + 20*y^3 - y^5) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp
    rw [h2, hpoly]
    norm_num
  · rw [Work.ZeroFreeTables.intCosPoly72 σ hσ]
    positivity

/-! ## The closed form at `s = 0` and for `Isub` -/

lemma RA72_zero (σ : ℝ) : RA72 0 σ = 4/σ^4 + 4/σ^6 := by
  rcases eq_or_ne σ 0 with h|h
  · subst h; simp [RA72]
  · simp only [RA72]; field_simp; ring

lemma RB72_zero (σ : ℝ) : RB72 0 σ = 4*(σ^2-1)/σ^6 := by
  rcases eq_or_ne σ 0 with h|h
  · subst h; simp [RB72]
  · simp only [RB72]; field_simp; ring

lemma RI72_zero (σ : ℝ) : RI72 0 σ = -(8/σ^5) := by
  rcases eq_or_ne σ 0 with h|h
  · subst h; simp [RI72]
  · simp only [RI72]; field_simp; ring

/-- **The closed form of `Re G72(iσ)`.** -/
theorem G72_re_closed_zero {σ : ℝ} (hσ : σ ≠ 0) :
    (G72 ((σ : ℂ) * Complex.I)).re
      = (4/σ^4 + 4/σ^6) + Real.cos (2*σ)*(4*(σ^2-1)/σ^6)
        + Real.sin (2*σ)*(-(8/σ^5)) := by
  have hρ : (0:ℝ)^2 + σ^2 ≠ 0 := by simpa using pow_ne_zero 2 hσ
  have h := G72ReClosed0 (s := 0) (σ := σ) hρ
  calc (G72 ((σ:ℂ)*Complex.I)).re
      = 4/σ^4 + 4/σ^6 + (Real.cos (2*σ) * (4*(σ^2-1)/σ^6)
          + -(Real.sin (2*σ) * (8/σ^5))) := by
        rw [RA72_zero, RB72_zero, RI72_zero] at h
        simpa using h
    _ = 4/σ^4 + 4/σ^6 + Real.cos (2*σ)*(4*(σ^2-1)/σ^6)
          + Real.sin (2*σ)*(-(8/σ^5)) := by ring

/-- **The closed form of `Isub`.** -/
theorem Isub_eq_closed {s σ : ℝ} (hσ : σ ≠ 0) (hρ : s^2 + σ^2 ≠ 0) :
    Isub s σ = (RA72 s σ - 2*(4/σ^4 + 4/σ^6))
      + Real.cos (2*σ)*(Real.exp (2*s)*RB72 s σ - 8*(σ^2-1)/σ^6)
      + Real.sin (2*σ)*(Real.exp (2*s)*RI72 s σ + 16/σ^5) := by
  have h1 := G72ReClosed0 (s := s) (σ := σ) hρ
  have h2 := G72_re_closed_zero hσ
  rw [Isub, h1, h2]
  ring



/-! ## A weighted moment integral (used by the `F`-method cells) -/

/-- The antiderivative of `(1 - a y - (a y)^2/2) y^2 g72 y`, as an explicit polynomial in `y`. -/
lemma integral_weight_g72 (a Y : ℝ) :
    (∫ y in (0:ℝ)..Y, (1 - a*y - (a*y)^2/2) * y^2 * g72 y)
      = (1/30) * ((32*Y^3/3 - 8*Y^5 + (10/3)*Y^6 - Y^8/8)
          - a * (8*Y^4 - (20/3)*Y^6 + (20/7)*Y^7 - Y^9/9)
          - (a^2/2) * ((32/5)*Y^5 - (40/7)*Y^7 + (5/2)*Y^8 - Y^10/10)) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => (1/30) * (32/3*z^3 - 8*z^5 + 10/3*z^6 - z^8/8
          - 8*a*z^4 + 20/3*a*z^6 - 20/7*a*z^7 + a/9*z^9
          - 16/5*a^2*z^5 + 20/7*a^2*z^7 - 5/4*a^2*z^8 + a^2/20*z^10))
      ((1 - a*y - (a*y)^2/2) * y^2 * g72 y) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => (32/3)*z^3) ((32/3)*(3*y^2)) y := by
      simpa using (hasDerivAt_pow 3 y).const_mul ((32:ℝ)/3)
    have h2 : HasDerivAt (fun z : ℝ => 8*z^5) (8*(5*y^4)) y := by
      simpa using (hasDerivAt_pow 5 y).const_mul (8:ℝ)
    have h3 : HasDerivAt (fun z : ℝ => (10/3)*z^6) ((10/3)*(6*y^5)) y := by
      simpa using (hasDerivAt_pow 6 y).const_mul ((10:ℝ)/3)
    have h4 : HasDerivAt (fun z : ℝ => z^8/8) (8*y^7/8) y := (hasDerivAt_pow 8 y).div_const 8
    have h5 : HasDerivAt (fun z : ℝ => (8*a)*z^4) ((8*a)*(4*y^3)) y := by
      simpa using (hasDerivAt_pow 4 y).const_mul (8*a)
    have h6 : HasDerivAt (fun z : ℝ => ((20/3)*a)*z^6) (((20/3)*a)*(6*y^5)) y := by
      simpa using (hasDerivAt_pow 6 y).const_mul ((20/3)*a)
    have h7 : HasDerivAt (fun z : ℝ => ((20/7)*a)*z^7) (((20/7)*a)*(7*y^6)) y := by
      simpa using (hasDerivAt_pow 7 y).const_mul ((20/7)*a)
    have h8 : HasDerivAt (fun z : ℝ => (a/9)*z^9) ((a/9)*(9*y^8)) y := by
      simpa using (hasDerivAt_pow 9 y).const_mul (a/9)
    have h9 : HasDerivAt (fun z : ℝ => ((16/5)*a^2)*z^5) (((16/5)*a^2)*(5*y^4)) y := by
      simpa using (hasDerivAt_pow 5 y).const_mul ((16/5)*a^2)
    have h10 : HasDerivAt (fun z : ℝ => ((20/7)*a^2)*z^7) (((20/7)*a^2)*(7*y^6)) y := by
      simpa using (hasDerivAt_pow 7 y).const_mul ((20/7)*a^2)
    have h11 : HasDerivAt (fun z : ℝ => ((5/4)*a^2)*z^8) (((5/4)*a^2)*(8*y^7)) y := by
      simpa using (hasDerivAt_pow 8 y).const_mul ((5/4)*a^2)
    have h12 : HasDerivAt (fun z : ℝ => (a^2/20)*z^10) ((a^2/20)*(10*y^9)) y := by
      simpa using (hasDerivAt_pow 10 y).const_mul (a^2/20)
    have hsum := (((((((((((h1.sub h2).add h3).sub h4).sub h5).add h6).sub h7).add h8).sub h9).add h10).sub h11).add h12).const_mul ((1:ℝ)/30)
    exact hsum.congr_deriv (by simp only [Work.ZeroFreeTables.g72]; ring)
  have hint : IntervalIntegrable (fun y : ℝ => (1 - a*y - (a*y)^2/2) * y^2 * g72 y)
      MeasureTheory.volume (0:ℝ) Y := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  ring

end Work.ZeroFreeTables.OffAxis
end
