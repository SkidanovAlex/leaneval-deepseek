import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Approx.modelDisp_second_order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

set_option maxHeartbeats 4000000

/-! ## Auxiliary estimates for the approximate Écalle step

This file proves `approxEcal_step`: the per-step error of the approximate perturbed
Fatou coordinate `Ũ(u) = u + (1-h₁)·log(sinh(a·u)/a)` is `O(‖ζ(u)‖² + λ²)` on the
transit strip.

The proof has two analytic ingredients.

* `sinh_modelDisp_identity`: the exact algebraic identity
  `sinh(a(u+Φ))/a · (1+A₂) = sinh(a·u)/a · e^{-aΦ}` (where `Φ = modelDisp` and
  `A₂ = (ζ+a)h(ζ)`), which is the `s = e^{2au}` substitution of the displacement
  formula.  Taking logarithms gives
  `log(sinh(a(u+Φ))/a) - log(sinh(a·u)/a) = -aΦ - log(1+A₂)`; the branch of the
  logarithm is pinned down by the hypothesis that `sinh(a(u+tΦ))/a` lies in the slit
  plane for all `t ∈ [0,1]` (so that `log` at the two ends may be compared through a
  bound on the imaginary part, `eq_of_exp_eq_of_im_lt`).
* `norm_S_le`: the algebraic second-order estimate for the remaining combination
  `1 - h + ζh² - κζh - κaζh²` with `h = h(ζ)`, `κ = 1-h₁`, using
  `h(ζ) = 1 + h₁ζ + O(ζ²)`. -/

/-- The six-term triangle inequality. -/
private lemma norm_six_le (x1 x2 x3 x4 x5 x6 : ℂ) :
    ‖x1 + x2 + x3 + x4 + x5 + x6‖ ≤ ‖x1‖+‖x2‖+‖x3‖+‖x4‖+‖x5‖+‖x6‖ := by
  calc ‖x1 + x2 + x3 + x4 + x5 + x6‖ ≤ ‖x1 + x2 + x3 + x4 + x5‖ + ‖x6‖ := norm_add_le _ _
    _ ≤ (‖x1 + x2 + x3 + x4‖ + ‖x5‖) + ‖x6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖x1 + x2 + x3‖ + ‖x4‖) + ‖x5‖) + ‖x6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖x1 + x2‖ + ‖x3‖) + ‖x4‖) + ‖x5‖) + ‖x6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((((‖x1‖ + ‖x2‖) + ‖x3‖) + ‖x4‖) + ‖x5‖) + ‖x6‖ := by gcongr; exact norm_add_le _ _
    _ = ‖x1‖+‖x2‖+‖x3‖+‖x4‖+‖x5‖+‖x6‖ := by ring

/-- **The second-order algebraic estimate.**  With `hz = h ζ`, `κ = 1-h₁`,
`hζ = 1 + h₁ζ + O(ζ²)` (in the form `‖hz - 1 - h1*ζ‖ ≤ A‖ζ‖²`) and `‖hz‖ ≤ 3/2`,
`‖ζ‖ ≤ 1/4`, `‖a‖ ≤ 1/4`:

`‖1 - hz + ζhz² - κζhz - κaζhz²‖ ≤ (A + ‖h₁‖(2+‖κ‖) + A/2 + ‖h₁‖²/4 + A‖h₁‖/8 + A²/64 + ‖κ‖A/4 + 9‖κ‖/8)·(‖ζ‖²+‖a‖²)`. -/
private lemma norm_S_le (ζ h1 hz a : ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hhe : ‖hz - 1 - h1*ζ‖ ≤ A*‖ζ‖^2) (hhz : ‖hz‖ ≤ 3/2)
    (hζ1 : ‖ζ‖ ≤ 1/4) (_ha1 : ‖a‖ ≤ 1/4) :
    ‖1 - hz + ζ*hz^2 - (1-h1)*ζ*hz - (1-h1)*a*ζ*hz^2‖
      ≤ (A + ‖h1‖*(2+‖1-h1‖) + A/2 + ‖h1‖^2/4 + A*‖h1‖/8 + A^2/64
          + ‖1-h1‖*A/4 + 9*‖1-h1‖/8) * (‖ζ‖^2 + ‖a‖^2) := by
  set e : ℂ := hz - 1 - h1*ζ with hedef
  have hhe' : ‖e‖ ≤ A*‖ζ‖^2 := by rw [hedef]; exact hhe
  have hzdecomp : hz = 1 + h1*ζ + e := by rw [hedef]; ring
  have hS : 1 - hz + ζ*hz^2 - (1-h1)*ζ*hz - (1-h1)*a*ζ*hz^2
      = (-e) + h1*(2-(1-h1))*ζ^2 + 2*ζ*e + ζ*(h1*ζ+e)^2 + (-((1-h1)*ζ*e))
        + (-((1-h1)*a*ζ*hz^2)) := by
    rw [hzdecomp]; ring
  rw [hS]
  have hb2 : ‖h1*(2-(1-h1))*ζ^2‖ ≤ ‖h1‖*(2+‖1-h1‖)*‖ζ‖^2 := by
    rw [norm_mul, norm_mul, norm_pow]
    have h2 : ‖2 - (1-h1)‖ ≤ 2 + ‖1-h1‖ := by
      calc ‖2 - (1-h1)‖ = ‖(2:ℂ) + -(1-h1)‖ := by ring_nf
        _ ≤ ‖(2:ℂ)‖ + ‖-(1-h1)‖ := norm_add_le _ _
        _ = 2 + ‖1-h1‖ := by rw [Complex.norm_ofNat, norm_neg]
    gcongr
  have hb3 : ‖2*ζ*e‖ ≤ (A/2)*‖ζ‖^2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖ζ‖ * ‖e‖ ≤ 2 * ‖ζ‖ * (A * ‖ζ‖^2) := by gcongr
      _ = (2*A*‖ζ‖^2) * ‖ζ‖ := by ring
      _ ≤ (2*A*‖ζ‖^2) * (1/4) := mul_le_mul_of_nonneg_left hζ1 (by positivity)
      _ = (A/2)*‖ζ‖^2 := by ring
  have hb4 : ‖ζ*(h1*ζ+e)^2‖ ≤ (‖h1‖^2/4 + A*‖h1‖/8 + A^2/64)*‖ζ‖^2 := by
    have h4 : ‖h1*ζ+e‖ ≤ ‖h1‖*‖ζ‖ + A*‖ζ‖^2 := by
      have hh := norm_add_le (h1*ζ) e
      rw [norm_mul] at hh
      linarith [hh, hhe']
    have h5 : ‖h1*ζ+e‖ ≤ (‖h1‖ + A/4)*‖ζ‖ := by
      have h6 : ‖h1‖*‖ζ‖ + A*‖ζ‖^2 = (‖h1‖ + A*‖ζ‖)*‖ζ‖ := by ring
      rw [h6] at h4
      have h7 : ‖h1‖ + A*‖ζ‖ ≤ ‖h1‖ + A/4 := by nlinarith [hζ1, hA]
      exact h4.trans (mul_le_mul_of_nonneg_right h7 (norm_nonneg ζ))
    calc ‖ζ*(h1*ζ+e)^2‖ = ‖ζ‖ * ‖h1*ζ+e‖^2 := by rw [norm_mul, norm_pow]
      _ ≤ ‖ζ‖ * ((‖h1‖ + A/4)*‖ζ‖)^2 := by gcongr
      _ = ((‖h1‖ + A/4)^2 * ‖ζ‖^2) * ‖ζ‖ := by ring
      _ ≤ ((‖h1‖ + A/4)^2 * ‖ζ‖^2) * (1/4) := mul_le_mul_of_nonneg_left hζ1 (by positivity)
      _ = (‖h1‖^2/4 + A*‖h1‖/8 + A^2/64)*‖ζ‖^2 := by ring
  have hb5 : ‖(1-h1)*ζ*e‖ ≤ (‖1-h1‖*A/4)*‖ζ‖^2 := by
    rw [norm_mul, norm_mul]
    calc ‖1-h1‖ * ‖ζ‖ * ‖e‖ ≤ ‖1-h1‖ * ‖ζ‖ * (A*‖ζ‖^2) := by gcongr
      _ = (‖1-h1‖*A*‖ζ‖^2) * ‖ζ‖ := by ring
      _ ≤ (‖1-h1‖*A*‖ζ‖^2) * (1/4) := mul_le_mul_of_nonneg_left hζ1 (by positivity)
      _ = (‖1-h1‖*A/4)*‖ζ‖^2 := by ring
  have hb6 : ‖(1-h1)*a*ζ*hz^2‖ ≤ (9*‖1-h1‖/8)*(‖ζ‖^2+‖a‖^2) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow]
    have hhz2 : ‖hz‖^2 ≤ 9/4 := by nlinarith [hhz, norm_nonneg hz]
    calc ‖1-h1‖ * ‖a‖ * ‖ζ‖ * ‖hz‖^2 ≤ ‖1-h1‖ * ‖a‖ * ‖ζ‖ * (9/4) := by gcongr
      _ = (9/4)*‖1-h1‖*(‖a‖*‖ζ‖) := by ring
      _ ≤ (9/4)*‖1-h1‖*((‖a‖^2+‖ζ‖^2)/2) := by
            gcongr; nlinarith [sq_nonneg (‖a‖ - ‖ζ‖)]
      _ = (9*‖1-h1‖/8)*(‖ζ‖^2+‖a‖^2) := by ring
  have htri : ‖(-e) + h1*(2-(1-h1))*ζ^2 + 2*ζ*e + ζ*(h1*ζ+e)^2 + (-((1-h1)*ζ*e))
      + (-((1-h1)*a*ζ*hz^2))‖
      ≤ ‖e‖ + ‖h1*(2-(1-h1))*ζ^2‖ + ‖2*ζ*e‖ + ‖ζ*(h1*ζ+e)^2‖
        + ‖(1-h1)*ζ*e‖ + ‖(1-h1)*a*ζ*hz^2‖ := by
    simpa only [norm_neg] using norm_six_le (-e) (h1*(2-(1-h1))*ζ^2) (2*ζ*e) (ζ*(h1*ζ+e)^2)
      (-((1-h1)*ζ*e)) (-((1-h1)*a*ζ*hz^2))
  refine htri.trans ?_
  have hcoef : 0 ≤ A + ‖h1‖*(2+‖1-h1‖) + A/2 + ‖h1‖^2/4 + A*‖h1‖/8 + A^2/64 + ‖1-h1‖*A/4 := by
    have h1' : 0 ≤ ‖h1‖*(2+‖1-h1‖) := by positivity
    have h2' : 0 ≤ ‖h1‖^2/4 := by positivity
    have h3' : 0 ≤ A*‖h1‖/8 := by positivity
    have h4' : 0 ≤ ‖1-h1‖*A/4 := by positivity
    nlinarith [hA, h1', h2', h3', h4']
  calc ‖e‖ + ‖h1*(2-(1-h1))*ζ^2‖ + ‖2*ζ*e‖ + ‖ζ*(h1*ζ+e)^2‖ + ‖(1-h1)*ζ*e‖
        + ‖(1-h1)*a*ζ*hz^2‖
      ≤ (A*‖ζ‖^2) + (‖h1‖*(2+‖1-h1‖)*‖ζ‖^2) + ((A/2)*‖ζ‖^2)
        + ((‖h1‖^2/4 + A*‖h1‖/8 + A^2/64)*‖ζ‖^2) + ((‖1-h1‖*A/4)*‖ζ‖^2)
        + ((9*‖1-h1‖/8)*(‖ζ‖^2+‖a‖^2)) := by gcongr
    _ ≤ (A + ‖h1‖*(2+‖1-h1‖) + A/2 + ‖h1‖^2/4 + A*‖h1‖/8 + A^2/64
          + ‖1-h1‖*A/4 + 9*‖1-h1‖/8) * (‖ζ‖^2 + ‖a‖^2) := by
        nlinarith [hcoef, mul_nonneg hcoef (sq_nonneg ‖a‖), sq_nonneg ‖ζ‖, sq_nonneg ‖a‖]

/-- For `a = λ·I` with `λ > 0` and `u` in the transit strip (`R ≤ Re u ≤ π/λ - R`,
`R ≥ 4`), the point `sinh(a·u)/a = sin(λu)/λ` has **strictly positive real part**.
This is the slit-plane / right-half-plane statement that puts the argument of the
Écalle coordinate's antiderivative in `(-π/2, π/2)`. -/
theorem sinh_mul_I_div_re_pos (lam R : ℝ) (hlam : 0 < lam) (hR : 4 ≤ R) (u : ℂ)
    (hu1 : R ≤ u.re) (hu2 : u.re ≤ Real.pi / lam - R) :
    0 < (Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I)).re := by
  have hsinh : Complex.sinh (((lam : ℂ) * I) * u) = Complex.sin ((lam : ℂ) * u) * I := by
    rw [show ((lam : ℂ) * I) * u = ((lam : ℂ) * u) * I by ring]
    exact Complex.sinh_mul_I ((lam : ℂ) * u)
  have hdiv : Complex.sin ((lam : ℂ) * u) * I / ((lam : ℂ) * I)
      = Complex.sin ((lam : ℂ) * u) / (lam : ℂ) :=
    mul_div_mul_right _ _ Complex.I_ne_zero
  rw [hsinh, hdiv, Complex.div_ofReal_re]
  have hsin_re : (Complex.sin ((lam:ℂ)*u)).re
      = Real.sin (lam*u.re) * Real.cosh (lam*u.im) := by
    have hdecomp : (lam:ℂ)*u = ((lam*u.re : ℝ) : ℂ) + ((lam*u.im : ℝ):ℂ) * I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hdecomp, Complex.sin_add_mul_I]
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hsin_re]
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have h1 : 0 < lam * u.re := mul_pos hlam (lt_of_lt_of_le hRpos hu1)
  have h5 : 0 < lam * R := mul_pos hlam hRpos
  have h3 : lam * (Real.pi / lam - R) = Real.pi - lam * R := by field_simp
  have h4 : lam * u.re ≤ Real.pi - lam * R :=
    (mul_le_mul_of_nonneg_left hu2 (le_of_lt hlam)).trans_eq h3
  have h2 : lam * u.re < Real.pi := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hc := Real.cosh_pos (lam * u.im)
  exact div_pos (mul_pos hs hc) hlam

/-- `sinh(z)·2 = e^{2z} - 1` in the form used to compare the two ends. -/
private lemma ecalE_sub_one (a v : ℂ) :
    ecalE a v - 1 = 2 * Complex.exp (a*v) * Complex.sinh (a*v) := by
  have h : ecalE a v = Complex.exp (a*v) * Complex.exp (a*v) := by
    rw [ecalE, ← Complex.exp_add]; ring_nf
  rw [h, Complex.sinh, Complex.exp_neg, div_eq_mul_inv]; field_simp

/-- **The key algebraic identity.**  With `Φ = modelDisp a h u`, `A₁ = dispNum1`,
`A₂ = dispNum2`:

`sinh(a(u+Φ))/a · (1+A₂) = sinh(a·u)/a · e^{-aΦ}`.

It is the `s = e^{2au}` substitution of the exact displacement formula: `s·A₁ = A₂`
(`ecalPt ± a = 2a·s^{±1/2}/(s-1)`) turns `e^{2a(u+Φ)}(1+A₂) = e^{2au}(1+A₁)` into
`(1+A₂)(e^{2a(u+Φ)}-1) = e^{2au}-1`, and `e^{2z}-1 = 2e^z sinh z` finishes. -/
theorem sinh_modelDisp_identity (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (h1 : 1 + dispNum1 a h u ≠ 0) (h2 : 1 + dispNum2 a h u ≠ 0) (hs : ecalE a u ≠ 1) :
    Complex.sinh (a * (u + modelDisp a h u)) / a * (1 + dispNum2 a h u)
      = Complex.sinh (a * u) / a * Complex.exp (-(a * modelDisp a h u)) := by
  have hEA : ecalE a u * dispNum1 a h u = dispNum2 a h u := by
    rw [dispNum1, dispNum2, ← mul_assoc]
    have hza : ecalE a u * (ecalPt a u - a) = ecalPt a u + a := by
      rw [ecalPt_sub a u hs, ecalPt_add a u hs]
      have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
      field_simp
    rw [hza]
  have hstep : (1 + dispNum2 a h u) * (ecalE a (u + modelDisp a h u) - 1) = ecalE a u - 1 := by
    have hEp : ecalE a (u + modelDisp a h u)
        = ecalE a u * ((1 + dispNum1 a h u) / (1 + dispNum2 a h u)) :=
      ecalE_add_modelDisp a h u ha h2 h1
    rw [hEp, mul_sub, mul_one]
    have hprod : (1 + dispNum2 a h u) * (ecalE a u * ((1 + dispNum1 a h u) / (1 + dispNum2 a h u)))
        = ecalE a u * (1 + dispNum1 a h u) := by
      rw [← mul_assoc, mul_comm (1 + dispNum2 a h u) (ecalE a u), mul_assoc,
        mul_div_cancel₀ (1 + dispNum1 a h u) h2]
    rw [hprod]
    calc ecalE a u * (1 + dispNum1 a h u) - (1 + dispNum2 a h u)
        = (ecalE a u - 1) + (ecalE a u * dispNum1 a h u - dispNum2 a h u) := by ring
      _ = ecalE a u - 1 := by rw [hEA]; ring
  have hconv : (1 + dispNum2 a h u)
      * (2 * Complex.exp (a*(u + modelDisp a h u)) * Complex.sinh (a*(u + modelDisp a h u)))
      = 2 * Complex.exp (a*u) * Complex.sinh (a*u) := by
    rw [← ecalE_sub_one a (u + modelDisp a h u), ← ecalE_sub_one a u]
    exact hstep
  have hgoal2 : (1 + dispNum2 a h u) * Complex.exp (a*(u + modelDisp a h u))
      * Complex.sinh (a*(u + modelDisp a h u))
      = Complex.exp (a*u) * Complex.sinh (a*u) := by
    have h2' : (2:ℂ) * ((1 + dispNum2 a h u) * Complex.exp (a*(u + modelDisp a h u))
        * Complex.sinh (a*(u + modelDisp a h u)))
        = 2 * (Complex.exp (a*u) * Complex.sinh (a*u)) := by
      have h := hconv; ring_nf at h ⊢; exact h
    exact mul_left_cancel₀ two_ne_zero h2'
  have hexp1 : Complex.exp (a*u)
      = Complex.exp (a*(u + modelDisp a h u)) * Complex.exp (-(a * modelDisp a h u)) := by
    rw [← Complex.exp_add]; ring_nf
  have hfinal : (1 + dispNum2 a h u) * Complex.sinh (a*(u + modelDisp a h u))
      = Complex.sinh (a*u) * Complex.exp (-(a * modelDisp a h u)) := by
    refine mul_left_cancel₀ (Complex.exp_ne_zero (a*(u + modelDisp a h u))) ?_
    rw [show Complex.exp (a*(u + modelDisp a h u))
          * ((1 + dispNum2 a h u) * Complex.sinh (a*(u + modelDisp a h u)))
        = Complex.exp (a*u) * Complex.sinh (a*u) by rw [← hgoal2]; ring]
    rw [show Complex.exp (a*(u + modelDisp a h u))
          * (Complex.sinh (a*u) * Complex.exp (-(a*modelDisp a h u)))
        = Complex.exp (a*u) * Complex.sinh (a*u) by rw [hexp1]; ring]
  rw [show Complex.sinh (a*(u + modelDisp a h u))/a * (1 + dispNum2 a h u)
      = ((1 + dispNum2 a h u) * Complex.sinh (a*(u + modelDisp a h u)))/a by ring, hfinal]
  ring

/-- If two complex numbers have the same exponential and the imaginary part of their
difference is `< 2π`, they are equal: the difference is an integral multiple of `2πi`
and the bound rules out every non-zero multiple. -/
theorem eq_of_exp_eq_of_im_lt (Δ P : ℂ) (h : Complex.exp Δ = Complex.exp P)
    (hb : |(Δ - P).im| < 2 * Real.pi) : Δ = P := by
  have h1 : Complex.exp (Δ - P) = 1 := by
    rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero P)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have h2 : (Δ - P).im = (n : ℝ) * (2 * Real.pi) := by
    rw [hn]; simp [Complex.mul_re, Complex.mul_im]
  rw [h2] at hb
  have h3 : |(n:ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hb
  have h4 : |(n:ℝ)| < 1 := by
    have hp : (0:ℝ) < 2*Real.pi := by positivity
    nlinarith [h3, hp]
  have h4' : |n| < 1 := by exact_mod_cast h4
  have h5 : n = 0 := Int.abs_lt_one_iff.mp h4'
  rw [h5] at hn
  simp at hn
  exact sub_eq_zero.mp hn

theorem approxEcal_step (h : ℂ → ℂ) (h1 : ℂ) (A r : ℝ) (hA : 0 ≤ A)
    (hb : ImplosionBounds h h1 A r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam R : ℝ) (a : ℂ), 0 < lam → a = (lam : ℂ) * I →
      ∀ u : ℂ, GoodTransit a h lam R u → ‖ecalPt a u‖ < r →
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          Complex.sinh (a * (u + (t : ℂ) * modelDisp a h u)) / a ∈ Complex.slitPlane) →
        ‖approxEcal a (1 - h1) (u + modelDisp a h u) - approxEcal a (1 - h1) u + 1‖
          ≤ C * (‖ecalPt a u‖ ^ 2 + lam ^ 2) := by
  let C : ℝ := A + ‖h1‖*(2+‖1-h1‖) + A/2 + ‖h1‖^2/4 + A*‖h1‖/8 + A^2/64
      + ‖1-h1‖*A/4 + 9*‖1-h1‖/8 + 32*(1 + ‖1-h1‖/4) + 9*‖1-h1‖/2
  have hC : 0 ≤ C := by
    have h1' : 0 ≤ ‖h1‖*(2+‖1-h1‖) := by positivity
    have h2' : 0 ≤ ‖h1‖^2/4 := by positivity
    have h3' : 0 ≤ A*‖h1‖/8 := by positivity
    have h4' : 0 ≤ ‖1-h1‖*A/4 := by positivity
    have h5' : 0 ≤ 9*‖1-h1‖/8 := by positivity
    have h6' : 0 ≤ 32*(1 + ‖1-h1‖/4) := by positivity
    have h7' : 0 ≤ 9*‖1-h1‖/2 := by positivity
    have h8' : 0 ≤ A^2/64 := by positivity
    dsimp only [C]
    nlinarith [hA, h1', h2', h3', h4', h5', h6', h7', h8']
  refine ⟨C, hC, ?_⟩
  intro lam R a hlam ha u hgt hzr hslit
  subst ha
  obtain ⟨hstrip, hR4, hsmall, hh1, hh2, hZslit⟩ := hgt
  rw [mem_transitStrip_iff] at hstrip
  obtain ⟨hstr1, hstr2⟩ := hstrip
  have hane : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hlam) Complex.I_ne_zero
  have hna : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hlam.le]
  set ζ := ecalPt ((lam : ℂ) * I) u with hζdef
  set Φ := modelDisp ((lam : ℂ) * I) h u with hΦdef
  simp only [approxEcal]
  set W : ℂ := Complex.sinh (((lam : ℂ) * I) * (u + Φ)) / ((lam : ℂ) * I) with hWdef
  set Z : ℂ := Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I) with hZdef
  have hsum : ‖ζ‖ + lam ≤ 1/4 := by linarith [hsmall]
  have hζle : ‖ζ‖ ≤ 1/4 := by linarith [hsum, hlam]
  have hlamle : lam ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hζ1 : ‖h ζ - 1‖ ≤ 1/2 := hh1
  have hζ2 : ‖h ζ‖ ≤ 2 := hh2
  have hζ3 : ‖h ζ‖ ≤ 3/2 := by
    have hh := norm_add_le (h ζ - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at hh
    linarith [hh, hζ1]
  have hζr : ‖ζ‖ < r := by simpa [← hζdef] using hzr
  have he : ‖h ζ - 1 - h1*ζ‖ ≤ A*‖ζ‖^2 := hb.1 ζ hζr
  have hRΦ : ‖Φ + h ζ - ζ*h ζ^2‖ ≤ 32*(‖ζ‖^2 + lam^2) := by
    have h4 : 4 * (‖ecalPt ((lam:ℂ)*I) u‖ + ‖((lam:ℂ)*I)‖) ≤ 1 := by
      have hζ' : ‖ecalPt ((lam:ℂ)*I) u‖ = ‖ζ‖ := by rw [← hζdef]
      rw [hζ', hna]; exact hsmall
    have hres := modelDisp_second_order ((lam:ℂ)*I) h u hane h4 hζ2
    simpa [← hΦdef, ← hζdef, hna] using hres
  have hΦn : ‖Φ‖ ≤ 65/16 := by
    have h1 : Φ = (Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2 := by ring
    have htri : ‖(Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2‖
        ≤ ‖Φ + h ζ - ζ*h ζ^2‖ + ‖h ζ‖ + ‖ζ*h ζ^2‖ := by
      have hadd := norm_add_le ((Φ + h ζ - ζ*h ζ^2) - h ζ) (ζ*h ζ^2)
      have hsub2 := norm_sub_le (Φ + h ζ - ζ*h ζ^2) (h ζ)
      linarith [hadd, hsub2]
    have h32 : 32*(‖ζ‖^2 + lam^2) ≤ 2 := by nlinarith [hsum, norm_nonneg ζ]
    have hz1 : ‖ζ*h ζ^2‖ ≤ (1/4)*(3/2)^2 := by
      rw [norm_mul, norm_pow]
      have h2 : ‖h ζ‖^2 ≤ (3/2)^2 := pow_le_pow_left₀ (norm_nonneg _) hζ3 2
      nlinarith [hζle, h2, norm_nonneg ζ]
    rw [h1]
    linarith [htri, hRΦ, h32, hz1, hζ3]
  have hA2decomp : dispNum2 ((lam:ℂ)*I) h u = (ζ + (lam:ℂ)*I) * h ζ := by
    rw [show dispNum2 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u + (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA1decomp : dispNum1 ((lam:ℂ)*I) h u = (ζ - (lam:ℂ)*I) * h ζ := by
    rw [show dispNum1 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u - (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA2le : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA2decomp, norm_mul]
    have h1' : ‖ζ + ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_add_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA2n : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA2le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA1le : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA1decomp, norm_mul]
    have h1' : ‖ζ - ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_sub_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA1n : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA1le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA2small : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 1/2 := by linarith
  have hA1ne : 1 + dispNum1 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum1 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA1n
    linarith
  have hA2ne : 1 + dispNum2 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum2 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA2n
    linarith
  have hEne : ecalE ((lam:ℂ)*I) u ≠ 1 := by
    intro hE
    have hmem : u ∈ periodLattice ((lam:ℂ)*I) := hE
    rw [mem_periodLattice_iff _ _ hane] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hratio : Real.pi * I / ((lam:ℂ)*I) = ((Real.pi/lam : ℝ) : ℂ) := by
      rw [mul_div_mul_right _ _ Complex.I_ne_zero]
      exact (Complex.ofReal_div _ _).symm
    rw [hratio] at hn
    have hure : u.re = (n:ℝ) * (Real.pi/lam) := by
      rw [hn]; simp [Complex.mul_re]
    have hπ : 0 < Real.pi/lam := div_pos Real.pi_pos hlam
    have h1' : (n:ℝ) * (Real.pi/lam) ≥ R := by rw [← hure]; exact hstr1
    have hpos : 0 < (n:ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [h1', hπ, hR4]
    have hposZ : (0:ℤ) < n := by exact_mod_cast hpos
    have hn1 : (1:ℤ) ≤ n := Int.lt_iff_add_one_le.mp hposZ
    have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h2' : u.re ≥ Real.pi/lam := by
      rw [hure]; nlinarith [hn1R, hπ]
    linarith [hstr2, h2']
  have hWslit : W ∈ Complex.slitPlane := by
    have hh := hslit 1 (by norm_num)
    simpa [hWdef, hΦdef] using hh
  have hZre : 0 < Z.re := by
    rw [hZdef]
    exact sinh_mul_I_div_re_pos lam R hlam hR4 u hstr1 hstr2
  have hWne : W ≠ 0 := Complex.slitPlane_ne_zero hWslit
  have hZne : Z ≠ 0 := Complex.slitPlane_ne_zero hZslit
  have hiden : W * (1 + dispNum2 ((lam:ℂ)*I) h u)
      = Z * Complex.exp (-(((lam:ℂ)*I) * Φ)) := by
    rw [hWdef, hZdef, hΦdef]
    exact sinh_modelDisp_identity ((lam:ℂ)*I) h u hane hA1ne hA2ne hEne
  have hΔ : Complex.log W - Complex.log Z
      = -(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by
    refine eq_of_exp_eq_of_im_lt (Complex.log W - Complex.log Z)
      (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) ?_ ?_
    · rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hWne, Complex.exp_log hZne,
        Complex.exp_log hA2ne]
      rw [div_eq_div_iff hZne hA2ne]
      rw [hiden]; ring
    · have hWpi : W.arg < Real.pi := by
        have hWslit' : 0 < W.re ∨ W.im ≠ 0 := hWslit
        rw [Complex.arg_lt_pi_iff]
        rcases hWslit' with hh | hh
        · exact Or.inl (le_of_lt hh)
        · exact Or.inr hh
      have hargW : |W.arg| < Real.pi := (abs_lt).mpr ⟨Complex.neg_pi_lt_arg W, hWpi⟩
      have hargZ : |Z.arg| < Real.pi/2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hZre)
      have hImval : ((Complex.log W - Complex.log Z)
          - (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))).im
          = W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
            + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im := by
        simp only [Complex.sub_im, Complex.neg_im, Complex.log_im]
        ring
      rw [hImval]
      have haΦ : |((((lam:ℂ)*I) * Φ)).im| ≤ lam*(65/16) := by
        calc |((((lam:ℂ)*I) * Φ)).im| ≤ ‖((lam:ℂ)*I) * Φ‖ := Complex.abs_im_le_norm _
          _ = ‖((lam:ℂ)*I)‖ * ‖Φ‖ := norm_mul _ _
          _ = lam * ‖Φ‖ := by rw [hna]
          _ ≤ lam*(65/16) := by gcongr
      have hLa2 : |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| ≤ 33/64 := by
        have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
          norm_log_one_add_sub_self_le_of_le_half hA2small
        have h1' : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖
            ≤ ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u‖ + ‖dispNum2 ((lam:ℂ)*I) h u‖ := by
          have h := norm_add_le (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u) (dispNum2 ((lam:ℂ)*I) h u)
          rwa [sub_add_cancel] at h
        have hnorm : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖ ≤ 33/64 := by
          nlinarith [h1', hlog, hA2n, sq_nonneg ‖dispNum2 ((lam:ℂ)*I) h u‖,
            norm_nonneg (dispNum2 ((lam:ℂ)*I) h u)]
        have h2 := Complex.abs_im_le_norm (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))
        linarith [h2, hnorm]
      have htri : |W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
          + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im|
          ≤ |W.arg - Z.arg| + |((((lam:ℂ)*I) * Φ)).im|
            + |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| := by
        have h1 := abs_add_le (W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im)
          ((Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im)
        have h2 := abs_add_le (W.arg - Z.arg) ((((lam:ℂ)*I) * Φ).im)
        linarith [h1, h2]
      have hsub : |W.arg - Z.arg| ≤ |W.arg| + |Z.arg| := by
        calc |W.arg - Z.arg| = |W.arg + (-Z.arg)| := by rw [sub_eq_add_neg]
          _ ≤ |W.arg| + |-Z.arg| := abs_add_le _ _
          _ = |W.arg| + |Z.arg| := by rw [abs_neg]
      have hpi : (49:ℝ)/16 < Real.pi := lt_trans (by norm_num) Real.pi_gt_d20
      linarith [htri, hsub, hargW, hargZ, haΦ, hLa2, hpi]
  have happrox : (u + Φ) + (1-h1)*Complex.log W - (u + (1-h1)*Complex.log Z) + 1
      = Φ + (1-h1)*(Complex.log W - Complex.log Z) + 1 := by ring
  rw [happrox, hΔ]
  have hsimpl : Φ + (1-h1)*(-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) + 1
      = (1 - (1-h1)*((lam:ℂ)*I))*Φ + 1
        - (1-h1)*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by ring
  rw [hsimpl]
  set S : ℂ := 1 - h ζ + ζ*(h ζ)^2 - (1-h1)*ζ*(h ζ) - (1-h1)*((lam:ℂ)*I)*ζ*(h ζ)^2 with hSdef
  have hdecomp : (1 - (1-h1)*((lam:ℂ)*I))*Φ + 1
        - (1-h1)*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
      = S + (1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - (1-h1)*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u) := by
    rw [hSdef, hA2decomp]; ring
  rw [hdecomp]
  have hSbound : ‖S‖ ≤ (A + ‖h1‖*(2+‖1-h1‖) + A/2 + ‖h1‖^2/4 + A*‖h1‖/8 + A^2/64
      + ‖1-h1‖*A/4 + 9*‖1-h1‖/8)*(‖ζ‖^2 + lam^2) := by
    rw [hSdef]
    have hres := norm_S_le ζ h1 (h ζ) ((lam:ℂ)*I) A hA he hζ3 hζle (by rw [hna]; exact hlamle)
    simpa [hna] using hres
  have hRΦb : ‖(1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
      ≤ 32*(1+‖1-h1‖/4)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hconst : ‖1 - (1-h1)*((lam:ℂ)*I)‖ ≤ 1 + ‖1-h1‖/4 := by
      calc ‖1 - (1-h1)*((lam:ℂ)*I)‖ ≤ ‖(1:ℂ)‖ + ‖(1-h1)*((lam:ℂ)*I)‖ := norm_sub_le _ _
        _ = 1 + ‖1-h1‖*lam := by rw [norm_one, norm_mul, hna]
        _ ≤ 1 + ‖1-h1‖/4 := by nlinarith [hlamle, norm_nonneg (1-h1)]
    calc ‖1 - (1-h1)*((lam:ℂ)*I)‖ * ‖Φ + h ζ - ζ*(h ζ)^2‖
        ≤ (1 + ‖1-h1‖/4) * (32*(‖ζ‖^2+lam^2)) := by gcongr
      _ = 32*(1+‖1-h1‖/4)*(‖ζ‖^2+lam^2) := by ring
  have hA22 : ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ (9/2)*(‖ζ‖^2 + lam^2) := by
    have h2 : ((‖ζ‖+lam)*(3/2))^2 ≤ (9/2)*(‖ζ‖^2+lam^2) := by
      nlinarith [sq_nonneg (‖ζ‖ - lam), norm_nonneg ζ]
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ ((‖ζ‖+lam)*(3/2))^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hA2le 2
      _ ≤ (9/2)*(‖ζ‖^2+lam^2) := h2
  have hE2b : ‖(1-h1)*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ (9*‖1-h1‖/2)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
      norm_log_one_add_sub_self_le_of_le_half hA2small
    calc ‖1-h1‖ * ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u‖
        ≤ ‖1-h1‖ * ‖dispNum2 ((lam:ℂ)*I) h u‖^2 := by gcongr
      _ ≤ ‖1-h1‖ * ((9/2)*(‖ζ‖^2+lam^2)) := by gcongr
      _ = (9*‖1-h1‖/2)*(‖ζ‖^2+lam^2) := by ring
  have hfin : ‖S + (1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - (1-h1)*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ C * (‖ζ‖^2 + lam^2) := by
    have htri2 : ‖S + (1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - (1-h1)*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖
        ≤ ‖S‖ + ‖(1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
          + ‖(1-h1)*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u)‖ := by
      have hsub3 := norm_sub_le (S + (1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
        ((1-h1)*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u))
      have hadd2 := norm_add_le S ((1 - (1-h1)*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
      linarith [hsub3, hadd2]
    refine htri2.trans ?_
    have hCexp : C = (A + ‖h1‖*(2+‖1-h1‖) + A/2 + ‖h1‖^2/4 + A*‖h1‖/8 + A^2/64
        + ‖1-h1‖*A/4 + 9*‖1-h1‖/8) + 32*(1+‖1-h1‖/4) + 9*‖1-h1‖/2 := by
      dsimp only [C]
    rw [hCexp]
    nlinarith [hSbound, hRΦb, hE2b, sq_nonneg ‖ζ‖, sq_nonneg lam]
  exact hfin

end Work.Implosion.Approx
