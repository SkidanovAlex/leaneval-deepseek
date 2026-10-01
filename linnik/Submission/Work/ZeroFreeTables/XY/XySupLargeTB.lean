/-
# ZeroFreeTables — XY/XySupLargeTB

The large-`t` sup-estimates of Xylouris §2 (order-2 case, i.e. HB (9.16) with `λ* = 1`):

  `xySup1 lam t = 14900 Re F(-1+it) - 30480 Re F(lam-1+it)`,
  `xySup2 lam t =  1250 Re F(-1+it) -  6000 Re F(lam-1+it)`

for HB Lemma 7.2's test function with `λ = 4/3` (`F = tf72Fc (4/3)`), are even in `t` and
satisfy `xySup1 ≤ 60`, `xySup2 ≤ 160` for `518/1000 ≤ lam ≤ 628/1000` and `t ≥ 13`.

## Structure of the proof

Write `β = 1 - lam ∈ [372/1000, 482/1000]`.  By the closed form `Tf72FcClosed` and its real
decomposition (`XyReDecompB`)

  `Re F(x + it) = ReQ x t + xyE x t`,
  `xyE x t = exp (-(3x/2)) (cos (3t/2) · ReP x t + sin (3t/2) · ImP x t)`,

so that

  `xySup1 lam t ≤ 14900 (ReQ (-1) t + |xyE (-1) t|) - 30480 (ReQ (-β) t - |xyE (-β) t|)`.

The three analytic ingredients are

* `xyReQ_neg1`:  `ReQ (-1) t ≤ -(64/45)/(1+t²) - (29/5)/t⁴`,
* `xyReQ_beta`:  `-(64/45)β/(β²+t²) + (33/10)/t⁴ ≤ ReQ (-β) t`,
* `xyExpPart`:   `|cos (3t/2) ReP x t + sin (3t/2) ImP x t| ≤ (1573888/123201)/t⁴`
  for `-1 ≤ x ≤ 0`,

and the exponential prefactors are bounded by `exp (3/2) ≤ 4482/1000`, `exp (723/1000) ≤
2061/1000` (`SupAux`).  Reducing every occurring `1/t⁴` and `1/(c+t²)` to a multiple of
`1/t²` (the elementary estimates at `t = 13`) leaves the two purely numerical inequalities
`xyArith60`/`xyArith160`, which are proved by `norm_num`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.SupDefs
import Submission.Work.ZeroFreeTables.XY.XyReDecompB
import Submission.Work.ZeroFreeTables.XY.XySupIntegral
import Submission.Work.ZeroFreeTables.XY.SupAux
import Submission.Work.ZeroFreeTables.XY.XyInvPowReIm

open MeasureTheory intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-! ## §1  Evenness in `t` -/

/-- `xyRe x t` is even in `t`. -/
lemma xyRe_neg_t (x t : ℝ) : xyRe x (-t) = xyRe x t := by
  rw [xyRe_eq_integral x (-t), xyRe_eq_integral x t]
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  rw [show (-t) * u = -(t * u) by ring, Real.cos_neg]

/-! ## §0  A division helper -/

private lemma div_le_div_aux {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [le_div_iff₀ hd, div_mul_eq_mul_div, div_le_iff₀ hb]
  exact h

/-! ## §2  `ReQ` at `x = -1` -/

/-- `ReQ (-1) t ≤ -(64/45)/(1+t²) - (29/5)/t⁴` for `t ≥ 13`. -/
lemma xyReQ_neg1 (t : ℝ) (ht : 13 ≤ t) :
    ReQ (-1) t ≤ -((64:ℝ)/45)/(1 + t^2) - (29/5)/t^4 := by
  set s : ℝ := t^2 with hsdef
  have hs : (169:ℝ) ≤ s := by rw [hsdef]; nlinarith
  have hs0 : (0:ℝ) < s := by linarith
  have h1s : (0:ℝ) < 1 + s := by linarith
  have ht4eq : t^4 = s^2 := by rw [hsdef]; ring
  rw [ht4eq]
  have hR : ReQ (-1) t = -((64:ℝ)/45)/(1+s) - ((512:ℝ)/81)*(3*s-1)/(1+s)^3
      + ((1024:ℝ)/81)*(s^2-6*s+1)/(1+s)^4
      + ((16384:ℝ)/729)*(s^3-15*s^2+15*s-1)/(1+s)^6 := by
    rw [ReQ]
    ring
  rw [hR]
  have key2 : ((2941:ℝ)/1000)*(1+s)^3 ≤ (3*s-1)*s^2 := by
    have hfac : 1000*(3*s-1)*s^2 - 2941*(1+s)^3
        = (s-169)*(59*s^2+148*s+16189) + 2733000 := by ring
    have h1 : (0:ℝ) ≤ s-169 := by linarith
    have h2 : (0:ℝ) ≤ 59*s^2+148*s+16189 := by nlinarith [hs]
    have h3 := mul_nonneg h1 h2
    linarith [hfac]
  have e2 : ((512:ℝ)/81)*((2941:ℝ)/1000)/s^2 ≤ ((512:ℝ)/81)*(3*s-1)/(1+s)^3 := by
    refine div_le_div_aux (by positivity) (by positivity) ?_
    nlinarith [key2]
  have e2' : -((512:ℝ)/81)*(3*s-1)/(1+s)^3 ≤ -((512:ℝ)/81)*((2941:ℝ)/1000)/s^2 := by
    rw [show -((512:ℝ)/81)*(3*s-1)/(1+s)^3 = -(((512:ℝ)/81)*(3*s-1)/(1+s)^3) by ring,
        show -((512:ℝ)/81)*((2941:ℝ)/1000)/s^2 = -(((512:ℝ)/81)*((2941:ℝ)/1000)/s^2) by ring]
    exact neg_le_neg e2
  have key3 : (s^2-6*s+1)*s^2 ≤ (1+s)^4 := by
    have hfac : (1+s)^4 - (s^2-6*s+1)*s^2 = 1+4*s+5*s^2+10*s^3 := by ring
    have h : (0:ℝ) ≤ 1+4*s+5*s^2+10*s^3 := by nlinarith [hs, sq_nonneg s]
    linarith [hfac]
  have e3 : ((1024:ℝ)/81)*(s^2-6*s+1)/(1+s)^4 ≤ ((1024:ℝ)/81)/s^2 := by
    refine div_le_div_aux (by positivity) (by positivity) ?_
    nlinarith [key3]
  have key4 : 169*(s^3-15*s^2+15*s-1)*s^2 ≤ (1+s)^6 := by
    have hfac : (1+s)^6 - 169*(s^3-15*s^2+15*s-1)*s^2
        = s^5*(s-163) + s^3*(2550*s-2515) + 184*s^2+6*s+1 := by ring
    have h1 : (0:ℝ) ≤ s^5*(s-163) := mul_nonneg (pow_nonneg (by linarith) 5) (by linarith)
    have h2 : (0:ℝ) ≤ s^3*(2550*s-2515) := mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)
    have h3 : (0:ℝ) ≤ 184*s^2+6*s+1 := by nlinarith [hs, sq_nonneg s]
    linarith [hfac]
  have e4 : ((16384:ℝ)/729)*(s^3-15*s^2+15*s-1)/(1+s)^6 ≤ ((16384:ℝ)/729/169)/s^2 := by
    refine div_le_div_aux (by positivity) (by positivity) ?_
    nlinarith [key4]
  have h1 : -(((512:ℝ)/81)*(3*s-1)/(1+s)^3)
      ≤ -(((512:ℝ)/81)*((2941:ℝ)/1000)/s^2) := neg_le_neg e2
  have h2 : (((1024:ℝ)/81)*(s^2-6*s+1))/(1+s)^4 ≤ (((1024:ℝ)/81)/s^2) := e3
  have h3 : (((16384:ℝ)/729)*(s^3-15*s^2+15*s-1))/(1+s)^6
      ≤ (((16384:ℝ)/729/169)/s^2) := e4
  have hsum := add_le_add (add_le_add h1 h2) h3
  have hcomb : -(((512:ℝ)/81)*((2941:ℝ)/1000)/s^2) + (((1024:ℝ)/81)/s^2)
        + (((16384:ℝ)/729/169)/s^2)
      = (-((512:ℝ)/81)*((2941:ℝ)/1000) + (1024:ℝ)/81 + (16384:ℝ)/729/169)/s^2 := by ring
  have hfin : (-((512:ℝ)/81)*((2941:ℝ)/1000) + (1024:ℝ)/81 + (16384:ℝ)/729/169)/s^2
      ≤ (-(29:ℝ)/5)/s^2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have htail : -(((512:ℝ)/81)*(3*s-1)/(1+s)^3) + (((1024:ℝ)/81)*(s^2-6*s+1))/(1+s)^4
      + (((16384:ℝ)/729)*(s^3-15*s^2+15*s-1))/(1+s)^6 ≤ (-(29:ℝ)/5)/s^2 := by
    calc -(((512:ℝ)/81)*(3*s-1)/(1+s)^3) + (((1024:ℝ)/81)*(s^2-6*s+1))/(1+s)^4
          + (((16384:ℝ)/729)*(s^3-15*s^2+15*s-1))/(1+s)^6
        ≤ -(((512:ℝ)/81)*((2941:ℝ)/1000)/s^2) + (((1024:ℝ)/81)/s^2)
          + (((16384:ℝ)/729/169)/s^2) := hsum
      _ = (-((512:ℝ)/81)*((2941:ℝ)/1000) + (1024:ℝ)/81 + (16384:ℝ)/729/169)/s^2 := hcomb
      _ ≤ (-(29:ℝ)/5)/s^2 := hfin
  have hL : -((64:ℝ)/45)/(1+s) - (((512:ℝ)/81)*(3*s-1)/(1+s)^3)
        + (((1024:ℝ)/81)*(s^2-6*s+1))/(1+s)^4
        + (((16384:ℝ)/729)*(s^3-15*s^2+15*s-1))/(1+s)^6
      = -((64:ℝ)/45)/(1+s) + (-(((512:ℝ)/81)*(3*s-1)/(1+s)^3)
        + (((1024:ℝ)/81)*(s^2-6*s+1))/(1+s)^4
        + (((16384:ℝ)/729)*(s^3-15*s^2+15*s-1))/(1+s)^6) := by ring
  rw [hL]
  rw [show -((64:ℝ)/45)/(1+s) - (29:ℝ)/5/s^2
      = -((64:ℝ)/45)/(1+s) + (-(29:ℝ)/5)/s^2 by ring]
  exact add_le_add (le_refl (-((64:ℝ)/45)/(1+s))) htail


/-! ## §3  `ReQ` at `x = -β` -/

/-- `-(64/45)β/(β²+t²) + (33/10)/t⁴ ≤ ReQ (-β) t` for `372/1000 ≤ β ≤ 482/1000`, `t ≥ 13`. -/
lemma xyReQ_beta (β t : ℝ) (hβ₁ : 372/1000 ≤ β) (hβ₂ : β ≤ 482/1000) (ht : 13 ≤ t) :
    -((64:ℝ)/45)*β/(β^2 + t^2) + (33/10)/t^4 ≤ ReQ (-β) t := by
  set s : ℝ := t^2 with hsdef
  have hs : (169:ℝ) ≤ s := by rw [hsdef]; nlinarith
  have hs0 : (0:ℝ) < s := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have hβ2 : β^2 ≤ 232324/1000000 := by nlinarith [hβ₁, hβ₂]
  have hbpos : (0:ℝ) < β^2 + s := by positivity
  have ht4eq : t^4 = s^2 := by rw [hsdef]; ring
  rw [ht4eq]
  have hR : ReQ (-β) t = -((64:ℝ)/45)*β/(β^2+s) + ((512:ℝ)/81)*β*(β^2-3*s)/(β^2+s)^3
      + ((1024:ℝ)/81)*(β^4-6*β^2*s+s^2)/(β^2+s)^4
      + ((16384:ℝ)/729)*(s^3-15*β^2*s^2+15*β^4*s-β^6)/(β^2+s)^6 := by
    rw [ReQ]
    ring
  rw [hR]
  have h23 : ((512:ℝ)/81)*β*(β^2-3*s)/(β^2+s)^3
        + ((1024:ℝ)/81)*(β^4-6*β^2*s+s^2)/(β^2+s)^4
      = ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2))/(β^2+s)^4 := by
    field_simp
    ring
  have h4nn : (0:ℝ) ≤ ((16384:ℝ)/729)*(s^3-15*β^2*s^2+15*β^4*s-β^6)/(β^2+s)^6 := by
    have hnum4 : (0:ℝ) ≤ s^3-15*β^2*s^2+15*β^4*s-β^6 := by
      have h1 : 15*β^2 ≤ s := by linarith [hβ2, hs]
      have h2 : β^2 ≤ 15*s := by linarith [hβ2, hs]
      have h3 : (0:ℝ) ≤ s^2*(s-15*β^2) := mul_nonneg (sq_nonneg s) (by linarith)
      have h4 : (0:ℝ) ≤ β^4*(15*s-β^2) := mul_nonneg (pow_nonneg hβ0.le 4) (by linarith)
      nlinarith [h3, h4]
    exact div_nonneg (mul_nonneg (by norm_num) hnum4) (by positivity)
  have hnum : (277:ℝ)/1000*s^2 - (151:ℝ)/100*s
      ≤ s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2) := by
    have hA : (277:ℝ)/1000 ≤ 1-(3/2)*β := by linarith
    have hB : 6*β^2+β^3 ≤ (151:ℝ)/100 := by nlinarith [hβ2, hβ₂]
    have hC : (0:ℝ) ≤ β^4+β^5/2 := by positivity
    have h1 : s^2*((277:ℝ)/1000) ≤ s^2*(1-(3/2)*β) :=
      mul_le_mul_of_nonneg_left hA (sq_nonneg s)
    have h2 : s*(6*β^2+β^3) ≤ s*((151:ℝ)/100) := mul_le_mul_of_nonneg_left hB hs0.le
    nlinarith [h1, h2, hC]
  have hden : (β^2+s)^4 ≤ (10056:ℝ)/10000*s^4 := by
    have h1 : β^2 + s ≤ (1+232324/1000000/169)*s := by nlinarith [hβ2, hs]
    have h2 : (1+232324/1000000/169)^4 ≤ (10056:ℝ)/10000 := by norm_num
    calc (β^2+s)^4 ≤ ((1+232324/1000000/169)*s)^4 := pow_le_pow_left₀ (by positivity) h1 4
      _ = (1+232324/1000000/169)^4 * s^4 := by ring
      _ ≤ (10056:ℝ)/10000*s^4 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have htail : (33:ℝ)/10/s^2
      ≤ ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2))/(β^2+s)^4 := by
    have hkey : (33:ℝ)/10/s^2
        ≤ ((1024:ℝ)/81)*((277:ℝ)/1000*s^2 - (151:ℝ)/100*s)/(β^2+s)^4 := by
      refine div_le_div_aux (by positivity) (by positivity) ?_
      calc (33:ℝ)/10*(β^2+s)^4 ≤ (33:ℝ)/10*((10056:ℝ)/10000*s^4) :=
            mul_le_mul_of_nonneg_left hden (by norm_num)
        _ = ((33:ℝ)/10*((10056:ℝ)/10000))*s^4 := by ring
        _ ≤ ((1024:ℝ)/81)*((277:ℝ)/1000*s^2 - (151:ℝ)/100*s)*s^2 := by
            have hlin : ((33:ℝ)/10*((10056:ℝ)/10000))*s
                ≤ ((1024:ℝ)/81)*((277:ℝ)/1000*s - (151:ℝ)/100) := by nlinarith [hs]
            have h3 := mul_le_mul_of_nonneg_right hlin (pow_nonneg hs0.le 3)
            nlinarith [h3]
    have hN : ((1024:ℝ)/81)*((277:ℝ)/1000*s^2 - (151:ℝ)/100*s)
        ≤ ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2)) :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    exact hkey.trans (div_le_div_of_nonneg_right hN (by positivity))
  have hstep : -((64:ℝ)/45)*β/(β^2+s) + (33:ℝ)/10/s^2
      ≤ -((64:ℝ)/45)*β/(β^2+s)
        + ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2))/(β^2+s)^4 :=
    add_le_add (le_refl _) htail
  have hstep2 : -((64:ℝ)/45)*β/(β^2+s)
        + ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2))/(β^2+s)^4
      ≤ -((64:ℝ)/45)*β/(β^2+s)
        + ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2))/(β^2+s)^4
        + ((16384:ℝ)/729)*(s^3-15*β^2*s^2+15*β^4*s-β^6)/(β^2+s)^6 :=
    le_add_of_nonneg_right h4nn
  have hstep3 := hstep.trans hstep2
  have hconv : -((64:ℝ)/45)*β/(β^2+s)
        + ((1024:ℝ)/81)*(s^2*(1-(3/2)*β) - s*(6*β^2+β^3) + (β^4+β^5/2))/(β^2+s)^4
        + ((16384:ℝ)/729)*(s^3-15*β^2*s^2+15*β^4*s-β^6)/(β^2+s)^6
      = -((64:ℝ)/45)*β/(β^2+s)
        + ((512:ℝ)/81)*β*(β^2-3*s)/(β^2+s)^3
        + ((1024:ℝ)/81)*(β^4-6*β^2*s+s^2)/(β^2+s)^4
        + ((16384:ℝ)/729)*(s^3-15*β^2*s^2+15*β^4*s-β^6)/(β^2+s)^6 := by
    rw [← h23]; ring
  rw [hconv] at hstep3
  exact hstep3


/-! ## §4  The exponential part -/

/-- The algebraic identity behind the complex form of the exponential part. -/
private lemma key_identity (w : ℂ) (hw : w ≠ 0) :
    (w + 4/3)^2 / w^6 = (w^4)⁻¹ + ((8/3 : ℝ) : ℂ) * (w^5)⁻¹
      + ((16/9 : ℝ) : ℂ) * (w^6)⁻¹ := by
  have h6 : w^6 ≠ 0 := pow_ne_zero 6 hw
  have h5 : w^5 ≠ 0 := pow_ne_zero 5 hw
  have h4 : w^4 ≠ 0 := pow_ne_zero 4 hw
  field_simp
  push_cast
  ring

private lemma re_ofReal_mul (a : ℝ) (w : ℂ) : ((a : ℂ) * w).re = a * w.re := by
  simp [Complex.mul_re]

private lemma im_ofReal_mul (a : ℝ) (w : ℂ) : ((a : ℂ) * w).im = a * w.im := by
  simp [Complex.mul_im]

/-- The complex form of the exponential part: `ReP + i·ImP = (1024/81)(z+4/3)²/z⁶`. -/
private lemma ReP_ImP_complex (x t : ℝ) (hxt : x^2 + t^2 ≠ 0) :
    ((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I)
      = (((1024:ℝ)/81 : ℝ) : ℂ)
        * (((((x:ℂ)+(t:ℂ)*Complex.I)) + 4/3)^2 / (((x:ℂ)+(t:ℂ)*Complex.I))^6) := by
  have hz : ((x:ℂ) + (t:ℂ)*Complex.I) ≠ 0 := by
    intro h
    apply hxt
    have hre : x = 0 := by simpa using congrArg Complex.re h
    have him : t = 0 := by simpa using congrArg Complex.im h
    rw [hre, him]; norm_num
  obtain ⟨h1,h3,h4re,h4im,h5re,h5im,h6re,h6im⟩ := XyInvPowReIm x t hxt
  rw [key_identity ((x:ℂ)+(t:ℂ)*Complex.I) hz]
  apply Complex.ext
  · rw [show ((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I).re = ReP x t by
      simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]]
    rw [re_ofReal_mul, Complex.add_re, Complex.add_re, re_ofReal_mul, re_ofReal_mul,
      h4re, h5re, h6re]
    unfold ReP
    ring
  · rw [show ((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I).im = ImP x t by
      simp [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]]
    rw [im_ofReal_mul, Complex.add_im, Complex.add_im, im_ofReal_mul, im_ofReal_mul,
      h4im, h5im, h6im]
    unfold ImP
    ring

/-- `|cos (3t/2) ReP x t + sin (3t/2) ImP x t| ≤ (1573888/123201)/t⁴` for `-1 ≤ x ≤ 0`,
`t ≥ 13`. -/
lemma xyExpPart (x t : ℝ) (hx₁ : -1 ≤ x) (hx₂ : x ≤ 0) (ht : 13 ≤ t) :
    |Real.cos (3*t/2) * ReP x t + Real.sin (3*t/2) * ImP x t|
      ≤ ((1573888:ℝ)/123201)/t^4 := by
  have ht0 : (0:ℝ) < t := by linarith
  have ht2 : (169:ℝ) ≤ t^2 := by nlinarith
  have hxt : x^2 + t^2 ≠ 0 := by nlinarith [sq_nonneg x, ht]
  have hzc : Complex.normSq ((x:ℂ) + (t:ℂ)*Complex.I) = x^2 + t^2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hzc4 : Complex.normSq (((x:ℂ) + (t:ℂ)*Complex.I) + 4/3) = (x+4/3)^2 + t^2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hmod : ‖((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I)‖ ≤ ((1573888:ℝ)/123201)/t^4 := by
    rw [ReP_ImP_complex x t hxt, Complex.norm_mul, Complex.norm_div]
    simp only [Complex.norm_pow]
    have hcast : ‖(((1024:ℝ)/81 : ℝ) : ℂ)‖ = (1024:ℝ)/81 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [hcast]
    have hnum : ‖((x:ℂ) + (t:ℂ)*Complex.I) + 4/3‖^2 ≤ (16:ℝ)/9 + t^2 := by
      rw [← Complex.normSq_eq_norm_sq, hzc4]
      nlinarith [hx₁, hx₂]
    have hden : t^6 ≤ ‖((x:ℂ) + (t:ℂ)*Complex.I)‖^6 := by
      have h1 : ‖((x:ℂ) + (t:ℂ)*Complex.I)‖^2 = x^2+t^2 := by
        rw [← Complex.normSq_eq_norm_sq]; exact hzc
      have h2 : ‖((x:ℂ) + (t:ℂ)*Complex.I)‖^6
          = (x^2+t^2)^3 := by
        rw [show ‖((x:ℂ) + (t:ℂ)*Complex.I)‖^6
              = (‖((x:ℂ) + (t:ℂ)*Complex.I)‖^2)^3 by ring, h1]
      rw [h2]
      have h3 : t^2 ≤ x^2+t^2 := by nlinarith [sq_nonneg x]
      calc t^6 = (t^2)^3 := by ring
        _ ≤ (x^2+t^2)^3 := pow_le_pow_left₀ (by positivity) h3 3
    have hmid : ‖((x:ℂ) + (t:ℂ)*Complex.I) + 4/3‖^2 / ‖((x:ℂ) + (t:ℂ)*Complex.I)‖^6
        ≤ ((16:ℝ)/9 + t^2)/t^6 :=
      (div_le_div_of_nonneg_right hnum (by positivity)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
    have hfin : ((16:ℝ)/9 + t^2)/t^6 ≤ ((1537:ℝ)/1521)/t^4 := by
      refine div_le_div_aux (by positivity) (by positivity) ?_
      have h : (16:ℝ)/9 + t^2 ≤ ((1537:ℝ)/1521)*t^2 := by nlinarith [ht2]
      have h2 := mul_le_mul_of_nonneg_right h (pow_nonneg ht0.le 4)
      linarith [h2]
    calc (1024:ℝ)/81 * (‖((x:ℂ) + (t:ℂ)*Complex.I) + 4/3‖^2 / ‖((x:ℂ) + (t:ℂ)*Complex.I)‖^6)
        ≤ (1024:ℝ)/81 * (((1537:ℝ)/1521)/t^4) :=
          mul_le_mul_of_nonneg_left (hmid.trans hfin) (by norm_num)
      _ = ((1573888:ℝ)/123201)/t^4 := by ring
  have hcs : |Real.cos (3*t/2) * ReP x t + Real.sin (3*t/2) * ImP x t|
      ≤ ‖((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I)‖ := by
    have h1 : (Real.cos (3*t/2) * ReP x t + Real.sin (3*t/2) * ImP x t)^2
        ≤ ReP x t^2 + ImP x t^2 := by
      nlinarith [sq_nonneg (Real.cos (3*t/2) * ImP x t - Real.sin (3*t/2) * ReP x t),
        Real.cos_sq_add_sin_sq (3*t/2)]
    have h2 : Complex.normSq ((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I)
        = ReP x t^2 + ImP x t^2 := by
      rw [Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have h3 : ‖((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I)‖^2 = ReP x t^2 + ImP x t^2 := by
      rw [← Complex.normSq_eq_norm_sq, h2]
    have h4 : ‖((ReP x t : ℂ) + (ImP x t : ℂ) * Complex.I)‖
        = Real.sqrt (ReP x t^2 + ImP x t^2) := by
      rw [← h3, Real.sqrt_sq (norm_nonneg _)]
    rw [h4]
    have h5 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h5
    exact h5
  exact hcs.trans hmod

/-! ## §5  The exponential part of `xyRe` -/

/-- The `exp (-(3x/2))`-weighted trigonometric part of `Re F(x+it)`. -/
def xyE (x t : ℝ) : ℝ :=
  Real.exp (-(3*x/2)) * (Real.cos (3*t/2) * ReP x t + Real.sin (3*t/2) * ImP x t)

/-- `|xyE (-1) t| ≤ (58266/1000)/t⁴` for `t ≥ 13`. -/
lemma xyE_neg1 (t : ℝ) (ht : 13 ≤ t) : |xyE (-1) t| ≤ ((58266:ℝ)/1000)/t^4 := by
  have hb := xyExpPart (-1) t (by norm_num) (by norm_num) ht
  have hK : ((1573888:ℝ)/123201) ≤ 13 := by norm_num
  have ht4 : (0:ℝ) < t^4 := by positivity
  have hb' : |Real.cos (3*t/2) * ReP (-1) t + Real.sin (3*t/2) * ImP (-1) t|
      ≤ 13/t^4 := (le_trans hb (div_le_div_of_nonneg_right hK ht4.le))
  have harg : xyE (-1) t
      = Real.exp (3/2) * (Real.cos (3*t/2) * ReP (-1) t + Real.sin (3*t/2) * ImP (-1) t) := by
    unfold xyE
    rw [show -(3*(-1:ℝ)/2) = (3:ℝ)/2 by norm_num]
  have hexp : Real.exp (3/2) ≤ ((4482:ℝ)/1000) := by
    have := exp_1_5_bounds.2; linarith
  rw [harg, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (3/2) * |Real.cos (3*t/2) * ReP (-1) t + Real.sin (3*t/2) * ImP (-1) t|
      ≤ ((4482:ℝ)/1000) * (13/t^4) :=
        mul_le_mul hexp hb' (abs_nonneg _) (by norm_num)
    _ = ((58266:ℝ)/1000)/t^4 := by ring

/-- `|xyE (-β) t| ≤ (26793/1000)/t⁴` for `372/1000 ≤ β ≤ 482/1000`, `t ≥ 13`. -/
lemma xyE_beta (β t : ℝ) (hβ₁ : 372/1000 ≤ β) (hβ₂ : β ≤ 482/1000) (ht : 13 ≤ t) :
    |xyE (-β) t| ≤ ((26793:ℝ)/1000)/t^4 := by
  have hb := xyExpPart (-β) t (by linarith) (by linarith) ht
  have hK : ((1573888:ℝ)/123201) ≤ 13 := by norm_num
  have ht4 : (0:ℝ) < t^4 := by positivity
  have hb' : |Real.cos (3*t/2) * ReP (-β) t + Real.sin (3*t/2) * ImP (-β) t|
      ≤ 13/t^4 := (le_trans hb (div_le_div_of_nonneg_right hK ht4.le))
  have harg : xyE (-β) t
      = Real.exp (3*β/2) * (Real.cos (3*t/2) * ReP (-β) t + Real.sin (3*t/2) * ImP (-β) t) := by
    unfold xyE
    rw [show -(3*(-β)/2) = 3*β/2 by ring]
  have hexp : Real.exp (3*β/2) ≤ ((2061:ℝ)/1000) := by
    have h1 : 3*β/2 ≤ (723:ℝ)/1000 := by linarith
    have h2 := Real.exp_le_exp.mpr h1
    have h3 := exp_723_bounds.2
    linarith
  rw [harg, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (3*β/2) * |Real.cos (3*t/2) * ReP (-β) t + Real.sin (3*t/2) * ImP (-β) t|
      ≤ ((2061:ℝ)/1000) * (13/t^4) :=
        mul_le_mul hexp hb' (abs_nonneg _) (by norm_num)
    _ = ((26793:ℝ)/1000)/t^4 := by ring

/-! ## §6  The two numerical inequalities -/

lemma xyArith60 (s β : ℝ) (hs : 169 ≤ s) (hβ₁ : 372/1000 ≤ β) (hβ₂ : β ≤ 482/1000) :
    -((953600:ℝ)/45)/(1+s) + ((1950720:ℝ)/45)*β/(β^2+s) + 1510000/s^2 ≤ 60 := by
  have hspos : (0:ℝ) < s := by linarith
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hbs : (0:ℝ) < β^2 + s := by positivity
  have hA : ((953600:ℝ)/45)*((169:ℝ)/170)/s ≤ ((953600:ℝ)/45)/(1+s) := by
    have key : ((169:ℝ)/170)/s ≤ 1/(1+s) := by
      rw [← sub_nonneg]
      have h : 1/(1+s) - ((169:ℝ)/170)/s = (s - 169)/(170*s*(1+s)) := by
        field_simp
        try ring
      rw [h]
      exact div_nonneg (by linarith) (by positivity)
    calc ((953600:ℝ)/45)*((169:ℝ)/170)/s = ((953600:ℝ)/45)*(((169:ℝ)/170)/s) := by ring
      _ ≤ ((953600:ℝ)/45)*(1/(1+s)) := mul_le_mul_of_nonneg_left key (by norm_num)
      _ = ((953600:ℝ)/45)/(1+s) := by ring
  have hB : β/(β^2+s) ≤ ((482:ℝ)/1000)/s := by
    rw [← sub_nonneg]
    have h : ((482:ℝ)/1000)/s - β/(β^2+s)
        = ((482:ℝ)/1000*(β^2+s) - β*s)/(s*(β^2+s)) := by
      field_simp
      try ring
    rw [h]
    exact div_nonneg (by nlinarith [hβ₂, sq_nonneg β, hspos]) (by positivity)
  have hC : (1510000:ℝ)/s^2 ≤ (1510000/169)/s := by
    rw [← sub_nonneg]
    have h : (1510000/169)/s - (1510000:ℝ)/s^2 = (1510000*s - 1510000*169)/(169*s^2) := by
      field_simp
      try ring
    rw [h]
    exact div_nonneg (by nlinarith [hs]) (by positivity)
  have e1 : -((953600:ℝ)/45)/(1+s) ≤ -(((953600:ℝ)/45)*((169:ℝ)/170)/s) := by
    have h := neg_le_neg hA
    have h2 : -(((953600:ℝ)/45)/(1+s)) = -((953600:ℝ)/45)/(1+s) := by ring
    rw [← h2]
    exact h
  have e2 : ((1950720:ℝ)/45)*β/(β^2+s) ≤ ((1950720:ℝ)/45)*(((482:ℝ)/1000)/s) := by
    rw [show ((1950720:ℝ)/45)*β/(β^2+s) = ((1950720:ℝ)/45)*(β/(β^2+s)) by ring]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have e4 : -(((953600:ℝ)/45)*((169:ℝ)/170)/s) + ((1950720:ℝ)/45)*(((482:ℝ)/1000)/s)
      + (1510000/169)/s
      = (-((953600:ℝ)/45)*((169:ℝ)/170) + ((1950720:ℝ)/45)*((482:ℝ)/1000)
          + 1510000/169)/s := by ring
  have hcomb : -((953600:ℝ)/45)/(1+s) + ((1950720:ℝ)/45)*β/(β^2+s) + 1510000/s^2
      ≤ (-((953600:ℝ)/45)*((169:ℝ)/170) + ((1950720:ℝ)/45)*((482:ℝ)/1000)
          + 1510000/169)/s := by
    linarith [e1, e2, hC, e4]
  have hK : (0:ℝ) ≤ -((953600:ℝ)/45)*((169:ℝ)/170) + ((1950720:ℝ)/45)*((482:ℝ)/1000)
      + 1510000/169 := by norm_num
  calc -((953600:ℝ)/45)/(1+s) + ((1950720:ℝ)/45)*β/(β^2+s) + 1510000/s^2
      ≤ (-((953600:ℝ)/45)*((169:ℝ)/170) + ((1950720:ℝ)/45)*((482:ℝ)/1000)
          + 1510000/169)/s := hcomb
    _ ≤ (-((953600:ℝ)/45)*((169:ℝ)/170) + ((1950720:ℝ)/45)*((482:ℝ)/1000)
          + 1510000/169)/169 := div_le_div_of_nonneg_left hK (by norm_num) hs
    _ ≤ 60 := by norm_num

lemma xyArith160 (s β : ℝ) (hs : 169 ≤ s) (hβ₁ : 372/1000 ≤ β) (hβ₂ : β ≤ 482/1000) :
    -((80000:ℝ)/45)/(1+s) + ((384000:ℝ)/45)*β/(β^2+s) + 210000/s^2 ≤ 160 := by
  have hspos : (0:ℝ) < s := by linarith
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hbs : (0:ℝ) < β^2 + s := by positivity
  have hA : ((80000:ℝ)/45)*((169:ℝ)/170)/s ≤ ((80000:ℝ)/45)/(1+s) := by
    have key : ((169:ℝ)/170)/s ≤ 1/(1+s) := by
      rw [← sub_nonneg]
      have h : 1/(1+s) - ((169:ℝ)/170)/s = (s - 169)/(170*s*(1+s)) := by
        field_simp
        try ring
      rw [h]
      exact div_nonneg (by linarith) (by positivity)
    calc ((80000:ℝ)/45)*((169:ℝ)/170)/s = ((80000:ℝ)/45)*(((169:ℝ)/170)/s) := by ring
      _ ≤ ((80000:ℝ)/45)*(1/(1+s)) := mul_le_mul_of_nonneg_left key (by norm_num)
      _ = ((80000:ℝ)/45)/(1+s) := by ring
  have hB : β/(β^2+s) ≤ ((482:ℝ)/1000)/s := by
    rw [← sub_nonneg]
    have h : ((482:ℝ)/1000)/s - β/(β^2+s)
        = ((482:ℝ)/1000*(β^2+s) - β*s)/(s*(β^2+s)) := by
      field_simp
      try ring
    rw [h]
    exact div_nonneg (by nlinarith [hβ₂, sq_nonneg β, hspos]) (by positivity)
  have hC : (210000:ℝ)/s^2 ≤ (210000/169)/s := by
    rw [← sub_nonneg]
    have h : (210000/169)/s - (210000:ℝ)/s^2 = (210000*s - 210000*169)/(169*s^2) := by
      field_simp
      try ring
    rw [h]
    exact div_nonneg (by nlinarith [hs]) (by positivity)
  have e1 : -((80000:ℝ)/45)/(1+s) ≤ -(((80000:ℝ)/45)*((169:ℝ)/170)/s) := by
    have h := neg_le_neg hA
    have h2 : -(((80000:ℝ)/45)/(1+s)) = -((80000:ℝ)/45)/(1+s) := by ring
    rw [← h2]
    exact h
  have e2 : ((384000:ℝ)/45)*β/(β^2+s) ≤ ((384000:ℝ)/45)*(((482:ℝ)/1000)/s) := by
    rw [show ((384000:ℝ)/45)*β/(β^2+s) = ((384000:ℝ)/45)*(β/(β^2+s)) by ring]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have e4 : -(((80000:ℝ)/45)*((169:ℝ)/170)/s) + ((384000:ℝ)/45)*(((482:ℝ)/1000)/s)
      + (210000/169)/s
      = (-((80000:ℝ)/45)*((169:ℝ)/170) + ((384000:ℝ)/45)*((482:ℝ)/1000)
          + 210000/169)/s := by ring
  have hcomb : -((80000:ℝ)/45)/(1+s) + ((384000:ℝ)/45)*β/(β^2+s) + 210000/s^2
      ≤ (-((80000:ℝ)/45)*((169:ℝ)/170) + ((384000:ℝ)/45)*((482:ℝ)/1000)
          + 210000/169)/s := by
    linarith [e1, e2, hC, e4]
  have hK : (0:ℝ) ≤ -((80000:ℝ)/45)*((169:ℝ)/170) + ((384000:ℝ)/45)*((482:ℝ)/1000)
      + 210000/169 := by norm_num
  calc -((80000:ℝ)/45)/(1+s) + ((384000:ℝ)/45)*β/(β^2+s) + 210000/s^2
      ≤ (-((80000:ℝ)/45)*((169:ℝ)/170) + ((384000:ℝ)/45)*((482:ℝ)/1000)
          + 210000/169)/s := hcomb
    _ ≤ (-((80000:ℝ)/45)*((169:ℝ)/170) + ((384000:ℝ)/45)*((482:ℝ)/1000)
          + 210000/169)/169 := div_le_div_of_nonneg_left hK (by norm_num) hs
    _ ≤ 160 := by norm_num

/-! ## §7  Assembly -/

theorem XySupLargeTB :
    (∀ (lam t : ℝ), Work.ZeroFreeTables.xySup1 lam (-t) = Work.ZeroFreeTables.xySup1 lam t)
  ∧ (∀ (lam t : ℝ), Work.ZeroFreeTables.xySup2 lam (-t) = Work.ZeroFreeTables.xySup2 lam t)
  ∧ (∀ (lam t : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 → 13 ≤ t → Work.ZeroFreeTables.xySup1 lam t ≤ 60)
  ∧ (∀ (lam t : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 → 13 ≤ t → Work.ZeroFreeTables.xySup2 lam t ≤ 160) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam t
    simp only [xySup1, xyRe_neg_t]
  · intro lam t
    simp only [xySup2, xyRe_neg_t]
  · intro lam t h₁ h₂ ht
    have hβ₁ : (372:ℝ)/1000 ≤ 1 - lam := by linarith
    have hβ₂ : 1 - lam ≤ (482:ℝ)/1000 := by linarith
    have ht4 : (0:ℝ) < t^4 := by positivity
    have ht2 : (169:ℝ) ≤ t^2 := by nlinarith
    have hxt₁ : (-1:ℝ)^2 + t^2 ≠ 0 := by nlinarith [sq_nonneg t]
    have hxt₂ : (-(1-lam))^2 + t^2 ≠ 0 := by nlinarith [sq_nonneg (1-lam), ht]
    have d1 := XyReDecompB (-1) t hxt₁
    have d2 := XyReDecompB (-(1-lam)) t hxt₂
    have R1 : ReQ (-1) t ≤ -((64:ℝ)/45)/(1+t^2) - (29/5)/t^4 := xyReQ_neg1 t ht
    have R2 : -((64:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) + (33/10)/t^4 ≤ ReQ (-(1-lam)) t :=
      xyReQ_beta (1-lam) t hβ₁ hβ₂ ht
    have E1 : |xyE (-1) t| ≤ ((58266:ℝ)/1000)/t^4 := xyE_neg1 t ht
    have E2 : |xyE (-(1-lam)) t| ≤ ((26793:ℝ)/1000)/t^4 := xyE_beta (1-lam) t hβ₁ hβ₂ ht
    have b1 : 14900 * ReQ (-1) t ≤ -((953600:ℝ)/45)/(1+t^2) - 86420/t^4 := by
      have h := mul_le_mul_of_nonneg_left R1 (by norm_num : (0:ℝ) ≤ 14900)
      calc 14900 * ReQ (-1) t ≤ 14900 * (-((64:ℝ)/45)/(1+t^2) - (29/5)/t^4) := h
        _ = -((953600:ℝ)/45)/(1+t^2) - 86420/t^4 := by ring
    have b2 : -30480 * ReQ (-(1-lam)) t
        ≤ ((1950720:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) - 100584/t^4 := by
      have h := mul_le_mul_of_nonneg_left R2 (by norm_num : (0:ℝ) ≤ 30480)
      calc -30480 * ReQ (-(1-lam)) t
          ≤ -30480 * (-((64:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) + (33/10)/t^4) := by linarith [h]
        _ = ((1950720:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) - 100584/t^4 := by ring
    have b3 : 14900 * xyE (-1) t ≤ 870000/t^4 := by
      have h := (abs_le.mp E1).2
      calc 14900 * xyE (-1) t ≤ 14900 * (((58266:ℝ)/1000)/t^4) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = (14900 * ((58266:ℝ)/1000))/t^4 := by ring
        _ ≤ 870000/t^4 :=
            div_le_div_of_nonneg_right (by norm_num : (14900:ℝ) * (58266/1000) ≤ 870000) ht4.le
    have b4 : -30480 * xyE (-(1-lam)) t ≤ 820000/t^4 := by
      have h := (abs_le.mp E2).1
      have h' : -30480 * xyE (-(1-lam)) t ≤ 30480 * (((26793:ℝ)/1000)/t^4) := by
        have h2 : -xyE (-(1-lam)) t ≤ ((26793:ℝ)/1000)/t^4 := by linarith
        have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 30480)
        linarith [h3]
      calc -30480 * xyE (-(1-lam)) t ≤ 30480 * (((26793:ℝ)/1000)/t^4) := h'
        _ = (30480 * ((26793:ℝ)/1000))/t^4 := by ring
        _ ≤ 820000/t^4 :=
            div_le_div_of_nonneg_right (by norm_num : (30480:ℝ) * (26793/1000) ≤ 820000) ht4.le
    have expand : 14900 * (ReQ (-1) t + xyE (-1) t)
        - 30480 * (ReQ (-(1-lam)) t + xyE (-(1-lam)) t)
        = (14900 * ReQ (-1) t + 14900 * xyE (-1) t)
          - (30480 * ReQ (-(1-lam)) t + 30480 * xyE (-(1-lam)) t) := by ring
    have har := xyArith60 (t^2) (1-lam) ht2 hβ₁ hβ₂
    have har' : -((953600:ℝ)/45)/(1+t^2) + ((1950720:ℝ)/45)*(1-lam)/((1-lam)^2+t^2)
        + 1510000/t^4 ≤ 60 := by
      convert har using 2 <;> ring
    have hnum : (870000:ℝ)/t^4 + 820000/t^4 - 86420/t^4 - 100584/t^4 = 1502996/t^4 := by ring
    have hnum2 : (1502996:ℝ)/t^4 ≤ 1510000/t^4 :=
      div_le_div_of_nonneg_right (by norm_num : (1502996:ℝ) ≤ 1510000) ht4.le
    have hsup : xySup1 lam t = 14900 * xyRe (-1) t - 30480 * xyRe (-(1-lam)) t := by
      rw [xySup1, show lam - 1 = -(1 - lam) by ring]
    have dd1 : xyRe (-1) t = ReQ (-1) t + xyE (-1) t := d1
    have dd2 : xyRe (-(1-lam)) t = ReQ (-(1-lam)) t + xyE (-(1-lam)) t := d2
    rw [hsup, dd1, dd2]
    linarith [b1, b2, b3, b4, expand, har', hnum, hnum2]
  · intro lam t h₁ h₂ ht
    have hβ₁ : (372:ℝ)/1000 ≤ 1 - lam := by linarith
    have hβ₂ : 1 - lam ≤ (482:ℝ)/1000 := by linarith
    have ht4 : (0:ℝ) < t^4 := by positivity
    have ht2 : (169:ℝ) ≤ t^2 := by nlinarith
    have hxt₁ : (-1:ℝ)^2 + t^2 ≠ 0 := by nlinarith [sq_nonneg t]
    have hxt₂ : (-(1-lam))^2 + t^2 ≠ 0 := by nlinarith [sq_nonneg (1-lam), ht]
    have d1 := XyReDecompB (-1) t hxt₁
    have d2 := XyReDecompB (-(1-lam)) t hxt₂
    have R1 : ReQ (-1) t ≤ -((64:ℝ)/45)/(1+t^2) - (29/5)/t^4 := xyReQ_neg1 t ht
    have R2 : -((64:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) + (33/10)/t^4 ≤ ReQ (-(1-lam)) t :=
      xyReQ_beta (1-lam) t hβ₁ hβ₂ ht
    have E1 : |xyE (-1) t| ≤ ((58266:ℝ)/1000)/t^4 := xyE_neg1 t ht
    have E2 : |xyE (-(1-lam)) t| ≤ ((26793:ℝ)/1000)/t^4 := xyE_beta (1-lam) t hβ₁ hβ₂ ht
    have b1 : 1250 * ReQ (-1) t ≤ -((80000:ℝ)/45)/(1+t^2) - 7250/t^4 := by
      have h := mul_le_mul_of_nonneg_left R1 (by norm_num : (0:ℝ) ≤ 1250)
      calc 1250 * ReQ (-1) t ≤ 1250 * (-((64:ℝ)/45)/(1+t^2) - (29/5)/t^4) := h
        _ = -((80000:ℝ)/45)/(1+t^2) - 7250/t^4 := by ring
    have b2 : -6000 * ReQ (-(1-lam)) t
        ≤ ((384000:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) - 19800/t^4 := by
      have h := mul_le_mul_of_nonneg_left R2 (by norm_num : (0:ℝ) ≤ 6000)
      calc -6000 * ReQ (-(1-lam)) t
          ≤ -6000 * (-((64:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) + (33/10)/t^4) := by linarith [h]
        _ = ((384000:ℝ)/45)*(1-lam)/((1-lam)^2+t^2) - 19800/t^4 := by ring
    have b3 : 1250 * xyE (-1) t ≤ 73000/t^4 := by
      have h := (abs_le.mp E1).2
      calc 1250 * xyE (-1) t ≤ 1250 * (((58266:ℝ)/1000)/t^4) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = (1250 * ((58266:ℝ)/1000))/t^4 := by ring
        _ ≤ 73000/t^4 :=
            div_le_div_of_nonneg_right (by norm_num : (1250:ℝ) * (58266/1000) ≤ 73000) ht4.le
    have b4 : -6000 * xyE (-(1-lam)) t ≤ 161000/t^4 := by
      have h := (abs_le.mp E2).1
      have h' : -6000 * xyE (-(1-lam)) t ≤ 6000 * (((26793:ℝ)/1000)/t^4) := by
        have h2 : -xyE (-(1-lam)) t ≤ ((26793:ℝ)/1000)/t^4 := by linarith
        have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 6000)
        linarith [h3]
      calc -6000 * xyE (-(1-lam)) t ≤ 6000 * (((26793:ℝ)/1000)/t^4) := h'
        _ = (6000 * ((26793:ℝ)/1000))/t^4 := by ring
        _ ≤ 161000/t^4 :=
            div_le_div_of_nonneg_right (by norm_num : (6000:ℝ) * (26793/1000) ≤ 161000) ht4.le
    have expand : 1250 * (ReQ (-1) t + xyE (-1) t)
        - 6000 * (ReQ (-(1-lam)) t + xyE (-(1-lam)) t)
        = (1250 * ReQ (-1) t + 1250 * xyE (-1) t)
          - (6000 * ReQ (-(1-lam)) t + 6000 * xyE (-(1-lam)) t) := by ring
    have har := xyArith160 (t^2) (1-lam) ht2 hβ₁ hβ₂
    have har' : -((80000:ℝ)/45)/(1+t^2) + ((384000:ℝ)/45)*(1-lam)/((1-lam)^2+t^2)
        + 210000/t^4 ≤ 160 := by
      convert har using 2 <;> ring
    have hnum : (73000:ℝ)/t^4 + 161000/t^4 - 7250/t^4 - 19800/t^4 = 206950/t^4 := by ring
    have hnum2 : (206950:ℝ)/t^4 ≤ 210000/t^4 :=
      div_le_div_of_nonneg_right (by norm_num : (206950:ℝ) ≤ 210000) ht4.le
    have hsup : xySup2 lam t = 1250 * xyRe (-1) t - 6000 * xyRe (-(1-lam)) t := by
      rw [xySup2, show lam - 1 = -(1 - lam) by ring]
    have dd1 : xyRe (-1) t = ReQ (-1) t + xyE (-1) t := d1
    have dd2 : xyRe (-(1-lam)) t = ReQ (-(1-lam)) t + xyE (-(1-lam)) t := d2
    rw [hsup, dd1, dd2]
    linarith [b1, b2, b3, b4, expand, har', hnum, hnum2]

end Work.ZeroFreeTables.XY
