import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000

namespace Work.PARIMPL2.Direct

open Complex

/-! ## Elementary transcendental and numeric prerequisites -/

theorem log_ten_le_three : Real.log 10 ≤ 3 := by
  rw [Real.log_ten_eq]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem log_quarter_add_three (R : ℝ) (hR : 4 ≤ R) : Real.log R ≤ R / 4 + 3 := by
  have hR0 : 0 < R := by linarith
  have h1 : Real.log (R / 4) ≤ R / 4 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [Real.log_div (ne_of_gt hR0) (by norm_num : (4 : ℝ) ≠ 0)] at h1
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  linarith

theorem sinh_le_mul_exp (t : ℝ) (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.exp t := by
  have h1 : (1 - 2 * t) * Real.exp t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-2 * t)
    have hm := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos t))
    have he : Real.exp (-2 * t) * Real.exp t = Real.exp (-t) := by
      rw [← Real.exp_add]; ring_nf
    rw [he] at hm
    nlinarith [hm]
  have h2 : Real.exp t - Real.exp (-t) ≤ 2 * (t * Real.exp t) := by nlinarith [h1]
  rw [Real.sinh_eq]
  linarith

theorem sinh_le_three_mul (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Real.sinh t ≤ 3 * t := by
  have h := sinh_le_mul_exp t ht0
  have he : Real.exp t ≤ 3 :=
    le_of_lt (lt_of_le_of_lt (Real.exp_le_exp.mpr ht1) Real.exp_one_lt_three)
  nlinarith [h, he, ht0]

/-! ## The two logarithmic comparison lemmas -/

/-- Upper comparison. -/
theorem core_up (M c s u : ℝ) (hM : 0 < M) (hc : 0 < c) (hs : 0 < s) (hu : 0 ≤ u)
    (hMc : M ≤ 2 * c) (hcs : s ≤ 10 * c) :
    (1 / 2) * Real.log (M ^ 2 + u ^ 2)
      ≤ Real.log c + 10 + Real.log (1 + u / s) := by
  have hl2 : Real.log 2 ≤ (0.7 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog10 : Real.log 10 ≤ 3 := log_ten_le_three
  rcases lt_or_ge u M with hult | hMle
  · have hpos : 0 < M ^ 2 + u ^ 2 := by positivity
    have hle2 : M ^ 2 + u ^ 2 ≤ 2 * M ^ 2 := by nlinarith [hu, le_of_lt hult]
    have hlog1 : Real.log (M ^ 2 + u ^ 2) ≤ Real.log 2 + 2 * Real.log M := by
      have h := Real.log_le_log hpos hle2
      rw [Real.log_mul (by norm_num) (by positivity : M ^ 2 ≠ 0), Real.log_pow] at h
      simpa using h
    have hlogM : Real.log M ≤ Real.log 2 + Real.log c := by
      have h : Real.log M ≤ Real.log (2 * c) := Real.log_le_log hM (by linarith)
      rw [Real.log_mul (by norm_num) (ne_of_gt hc)] at h
      exact h
    have hlog1u : 0 ≤ Real.log (1 + u / s) :=
      Real.log_nonneg (by have : 0 ≤ u / s := div_nonneg hu (le_of_lt hs); linarith)
    linarith
  · have hu0 : 0 < u := lt_of_lt_of_le hM hMle
    have hpos : 0 < M ^ 2 + u ^ 2 := by positivity
    have hle2 : M ^ 2 + u ^ 2 ≤ 2 * u ^ 2 := by nlinarith [le_of_lt hM, hMle]
    have hlog1 : Real.log (M ^ 2 + u ^ 2) ≤ Real.log 2 + 2 * Real.log u := by
      have h := Real.log_le_log hpos hle2
      rw [Real.log_mul (by norm_num) (by positivity : u ^ 2 ≠ 0), Real.log_pow] at h
      simpa using h
    have hlogu : Real.log u - Real.log s ≤ Real.log (1 + u / s) := by
      have hstep : u / s ≤ 1 + u / s := by
        have : 0 ≤ u / s := div_nonneg (le_of_lt hu0) (le_of_lt hs); linarith
      have h := Real.log_le_log (div_pos hu0 hs) hstep
      rw [Real.log_div (ne_of_gt hu0) (ne_of_gt hs)] at h
      exact h
    have hlogs : Real.log s ≤ Real.log 10 + Real.log c := by
      have h : Real.log s ≤ Real.log (10 * c) := Real.log_le_log hs (by linarith)
      rw [Real.log_mul (by norm_num) (ne_of_gt hc)] at h
      exact h
    linarith

/-- Lower comparison. -/
theorem core_low (c N v : ℝ) (hc : 0 < c) (hN : 0 < N) (hv : 0 ≤ v)
    (hbound : N ^ 2 + v ^ 2 ≤ 1024 * c ^ 2) :
    (1 / 2) * Real.log (N ^ 2 + v ^ 2) - Real.log c ≤ 10 := by
  have hpos : 0 < N ^ 2 + v ^ 2 := by positivity
  have hlog : Real.log (N ^ 2 + v ^ 2) ≤ Real.log 1024 + 2 * Real.log c := by
    have h := Real.log_le_log hpos hbound
    rw [Real.log_mul (by norm_num : (1024 : ℝ) ≠ 0) (by positivity : c ^ 2 ≠ 0),
      Real.log_pow] at h
    simpa using h
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have hl2 : Real.log 2 ≤ (0.7 : ℝ) := by linarith [Real.log_two_lt_d9]
  linarith [hlog, h1024, hl2]

/-! ## Complex-sine modulus -/

theorem lse_sin_re (lam : ℝ) (u : ℂ) :
    (Complex.sin ((lam : ℂ) * u)).re = Real.sin (lam * u.re) * Real.cosh (lam * u.im) := by
  have hdecomp : (lam : ℂ) * u = ((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hkey : Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)
      = ((Real.sin (lam * u.re) * Real.cosh (lam * u.im) : ℝ) : ℂ)
        + ((Real.cos (lam * u.re) * Real.sinh (lam * u.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have h1 : (Complex.sin ((lam : ℂ) * u)).re
      = (Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)).re := by
    rw [hdecomp]
  rw [h1, hkey]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem lse_sin_im (lam : ℝ) (u : ℂ) :
    (Complex.sin ((lam : ℂ) * u)).im = Real.cos (lam * u.re) * Real.sinh (lam * u.im) := by
  have hdecomp : (lam : ℂ) * u = ((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hkey : Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)
      = ((Real.sin (lam * u.re) * Real.cosh (lam * u.im) : ℝ) : ℂ)
        + ((Real.cos (lam * u.re) * Real.sinh (lam * u.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have h1 : (Complex.sin ((lam : ℂ) * u)).im
      = (Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)).im := by
    rw [hdecomp]
  rw [h1, hkey]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem lse_sq_abs_sin (lam : ℝ) (u : ℂ) :
    ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2
      = Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, lse_sin_re, lse_sin_im]
  nlinarith [Real.cosh_sq (lam * u.im), Real.sin_sq_add_cos_sq (lam * u.re)]

theorem log_norm_sin (lam : ℝ) (u : ℂ) :
    Real.log ‖Complex.sin ((lam : ℂ) * u)‖
      = (1 / 2) * Real.log (Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) := by
  have hsq := lse_sq_abs_sin lam u
  have h2 : Real.log (‖Complex.sin ((lam : ℂ) * u)‖ ^ 2)
      = 2 * Real.log ‖Complex.sin ((lam : ℂ) * u)‖ := by
    rw [Real.log_pow]; norm_num
  rw [hsq] at h2
  linarith

/-! ## The endpoint estimate -/

theorem logSin_endpoints_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam*R^2 ≤ 1)
    (v w : ℂ) (hv1 : R/4+2 ≤ v.re) (hv2 : v.re ≤ R/4+4)
    (hw1 : Real.pi/lam - 2*R ≤ w.re) (hw2 : w.re ≤ Real.pi/lam - R/4)
    (hw3 : |w.im| ≤ R/4 + 4 + Real.log R) :
    |Real.log ‖Complex.sin ((lam:ℂ)*v)‖ - Real.log ‖Complex.sin ((lam:ℂ)*w)‖|
      ≤ 10 + Real.log (1 + Real.sinh (lam * |v.im|) / (lam * R)) := by
  have hR0 : 0 < R := by linarith
  rw [log_norm_sin lam v, log_norm_sin lam w]
  set s : ℝ := lam * R with hsdef
  set c : ℝ := s / (2 * Real.pi) with hcdef
  set M : ℝ := lam * (R/4 + 4) with hMdef
  set tw : ℝ := lam * (R/4 + 4 + Real.log R) with htwdef
  set xv : ℝ := lam * v.re with hxvdef
  set yv : ℝ := lam * v.im with hyvdef
  set xw : ℝ := lam * w.re with hxwdef
  set yw : ℝ := lam * w.im with hywdef
  set u : ℝ := Real.sinh (lam * |v.im|) with hudef
  set vv : ℝ := Real.sinh tw with hvdef
  have hlogR : Real.log R ≤ R/4 + 3 := log_quarter_add_three R (by linarith)
  -- basic positivity / size of s, c, M
  have hs : 0 < s := by rw [hsdef]; positivity
  have hc : 0 < c := by rw [hcdef]; positivity
  have hM : 0 < M := by rw [hMdef]; positivity
  have hsR : s * R ≤ 1 := by rw [hsdef]; nlinarith [hlamR]
  have hsle : s ≤ 1 / R := by rw [le_div_iff₀ hR0]; linarith [hsR]
  have hs128 : s ≤ 1/128 := by
    have h1 : (1:ℝ)/R ≤ 1/128 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 128) hR
    linarith
  have hs1 : s ≤ 1 := by linarith
  have h2c : 2 * c = s / Real.pi := by rw [hcdef]; ring_nf
  have h10c : 10 * c = 5 * s / Real.pi := by rw [hcdef]; ring_nf
  have hc_eq : c = (2/Real.pi) * (s/4) := by rw [hcdef]; ring_nf
  -- tw bounds
  have htw0 : 0 ≤ tw := by
    rw [htwdef]
    have : 0 < Real.log R := Real.log_pos (by linarith)
    positivity
  have htw_le : tw ≤ s := by
    rw [htwdef, hsdef]
    have h2 : R/4 + 4 + Real.log R ≤ R := by linarith [hlogR, hR]
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt hlam)
  -- M ≤ 2c and s ≤ 10c
  have hM2c : M ≤ 2 * c := by
    rw [h2c, hMdef, hsdef, le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2, hR, hlam, Real.pi_pos]
  have hcs10 : s ≤ 10 * c := by
    rw [h10c, le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2, hs]
  -- xv bounds
  have hxvlow : s/4 ≤ xv := by
    have h := mul_le_mul_of_nonneg_left hv1 (le_of_lt hlam)
    have he : lam * (R/4 + 2) = lam*R/4 + 2*lam := by ring
    rw [he] at h
    rw [hxvdef, hsdef]
    linarith [h, hlam]
  have hxv_le_M : xv ≤ M := by
    rw [hxvdef, hMdef]
    exact mul_le_mul_of_nonneg_left hv2 (le_of_lt hlam)
  have hxv0 : 0 ≤ xv := by linarith [hxvlow, hs]
  have h2c_le_one : 2 * c ≤ 1 := by
    rw [h2c, div_le_iff₀ Real.pi_pos]
    linarith [hs1, Real.pi_gt_three]
  have hxv_pi2 : xv ≤ Real.pi / 2 := by
    linarith [hxv_le_M, hM2c, h2c_le_one, Real.pi_gt_three]
  have hsin_xv_ge : c ≤ Real.sin xv := by
    rw [hc_eq]
    have h1 := Real.mul_le_sin hxv0 hxv_pi2
    have h2 := mul_le_mul_of_nonneg_left hxvlow (by positivity : (0:ℝ) ≤ 2/Real.pi)
    linarith
  have hsin_xv_le : Real.sin xv ≤ M := by
    have h := Real.sin_le hxv0
    linarith [h, hxv_le_M]
  -- xw bounds
  have hxwlow : Real.pi - 2*s ≤ xw := by
    have h := mul_le_mul_of_nonneg_left hw1 (le_of_lt hlam)
    have he : lam * (Real.pi / lam - 2*R) = Real.pi - 2*(lam*R) := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
    rw [he] at h
    rw [hxwdef, hsdef]
    linarith [h]
  have hxwhigh : xw ≤ Real.pi - s/4 := by
    have h := mul_le_mul_of_nonneg_left hw2 (le_of_lt hlam)
    have he : lam * (Real.pi / lam - R/4) = Real.pi - (lam*R)/4 := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
    rw [he] at h
    rw [hxwdef, hsdef]
    linarith [h]
  have hsin_xw_ge : c ≤ Real.sin xw := by
    have hxw0 : 0 ≤ Real.pi - xw := by linarith [hxwhigh, hs]
    have hxw_le : Real.pi - xw ≤ Real.pi/2 := by linarith [hxwlow, hs128, Real.pi_gt_three]
    have h1 : (2/Real.pi) * (Real.pi - xw) ≤ Real.sin (Real.pi - xw) := Real.mul_le_sin hxw0 hxw_le
    rw [Real.sin_pi_sub] at h1
    have h2 : (2/Real.pi)*(s/4) ≤ (2/Real.pi)*(Real.pi - xw) :=
      mul_le_mul_of_nonneg_left (by linarith [hxwhigh]) (by positivity : (0:ℝ) ≤ 2/Real.pi)
    rw [hc_eq]
    linarith
  have hsin_xw_le : Real.sin xw ≤ 2*s := by
    have hxw0 : 0 ≤ Real.pi - xw := by linarith [hxwhigh, hs]
    have h1 : Real.sin xw = Real.sin (Real.pi - xw) := (Real.sin_pi_sub xw).symm
    have h2 : Real.sin (Real.pi - xw) ≤ Real.pi - xw := Real.sin_le hxw0
    have h3 : Real.pi - xw ≤ 2*s := by linarith [hxwlow]
    rw [h1]
    linarith [h2, h3]
  -- u, vv facts
  have hu : 0 ≤ u := by rw [hudef]; exact Real.sinh_nonneg_iff.mpr (by positivity)
  have hv0 : 0 ≤ vv := Real.sinh_nonneg_iff.mpr htw0
  have hsinhyv : Real.sinh yv ^ 2 = u ^ 2 := by
    have hyvabs : |yv| = lam * |v.im| := by rw [hyvdef, abs_mul, abs_of_pos hlam]
    have h2 : Real.sinh yv ^ 2 = (Real.sinh |yv|)^2 := by
      rw [← sq_abs (Real.sinh yv), Real.abs_sinh]
    rw [h2, hyvabs, hudef]
  have hsinhyw_le : Real.sinh yw ^ 2 ≤ vv ^ 2 := by
    have hywabs : |yw| ≤ tw := by
      rw [hywdef, htwdef]
      calc |lam * w.im| = lam * |w.im| := by rw [abs_mul, abs_of_pos hlam]
        _ ≤ lam * (R/4+4+Real.log R) := mul_le_mul_of_nonneg_left hw3 (le_of_lt hlam)
    have h1 : Real.sinh |yw| ≤ vv := by rw [hvdef]; exact Real.sinh_le_sinh.mpr hywabs
    have h0 : 0 ≤ Real.sinh |yw| := Real.sinh_nonneg_iff.mpr (abs_nonneg yw)
    have h2 : Real.sinh yw ^ 2 = (Real.sinh |yw|)^2 := by
      rw [← sq_abs (Real.sinh yw), Real.abs_sinh]
    rw [h2]
    nlinarith [h1, h0]
  -- positivity of A and B
  have hApos : 0 < Real.sin xv ^ 2 + Real.sinh yv ^ 2 := by
    have h0 : 0 < Real.sin xv := lt_of_lt_of_le hc hsin_xv_ge
    nlinarith [h0]
  have hBpos : 0 < Real.sin xw ^ 2 + Real.sinh yw ^ 2 := by
    have h0 : 0 < Real.sin xw := lt_of_lt_of_le hc hsin_xw_ge
    nlinarith [h0]
  -- the comparison bounds
  have hAY_le : Real.sin xv ^ 2 + Real.sinh yv ^ 2 ≤ M ^ 2 + u ^ 2 := by
    have hsx0 : 0 ≤ Real.sin xv := le_of_lt (lt_of_lt_of_le hc hsin_xv_ge)
    have hsq : Real.sin xv ^ 2 ≤ M ^ 2 := by nlinarith [hsx0, hsin_xv_le, hM]
    nlinarith [hsq, hsinhyv]
  have hB_le : Real.sin xw ^ 2 + Real.sinh yw ^ 2 ≤ (2*s) ^ 2 + vv ^ 2 := by
    have hsx0 : 0 ≤ Real.sin xw := le_of_lt (lt_of_lt_of_le hc hsin_xw_ge)
    have hsq : Real.sin xw ^ 2 ≤ (2*s) ^ 2 := by nlinarith [hsx0, hsin_xw_le, hs]
    nlinarith [hsq, hsinhyw_le]
  have hA_ge : c ^ 2 ≤ Real.sin xv ^ 2 + Real.sinh yv ^ 2 := by
    have hc0 : 0 ≤ c := le_of_lt hc
    nlinarith [hsin_xv_ge, hc0, sq_nonneg (Real.sinh yv)]
  have hB_ge : c ^ 2 ≤ Real.sin xw ^ 2 + Real.sinh yw ^ 2 := by
    have hc0 : 0 ≤ c := le_of_lt hc
    nlinarith [hsin_xw_ge, hc0, sq_nonneg (Real.sinh yw)]
  -- hbound for core_low
  have hv3 : vv ≤ 3 * s := by
    have h1 : vv ≤ 3 * tw := by
      rw [hvdef]; exact sinh_le_three_mul tw htw0 (by linarith [htw_le, hs128])
    linarith [htw_le]
  have hbound : (2*s) ^ 2 + vv ^ 2 ≤ 1024 * c ^ 2 := by
    have hc7 : s/7 ≤ c := by
      rw [hcdef]
      exact div_le_div_of_nonneg_left (le_of_lt hs) (by positivity) (by linarith [Real.pi_lt_d2])
    have hc7sq : (s/7) ^ 2 ≤ c ^ 2 := by nlinarith [hc7, hs, hc]
    nlinarith [hc7sq, hv3, hv0, sq_nonneg s, hs]
  -- assemble
  have hXY : (1 / 2) * Real.log (Real.sin xv ^ 2 + Real.sinh yv ^ 2)
      - (1 / 2) * Real.log (Real.sin xw ^ 2 + Real.sinh yw ^ 2)
      ≤ 10 + Real.log (1 + u / s) := by
    have h1 : (1 / 2) * Real.log (Real.sin xv ^ 2 + Real.sinh yv ^ 2)
        ≤ (1 / 2) * Real.log (M ^ 2 + u ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hApos hAY_le) (by norm_num)
    have h2 : Real.log c ≤ (1 / 2) * Real.log (Real.sin xw ^ 2 + Real.sinh yw ^ 2) := by
      have hc2 : 0 < c ^ 2 := pow_pos hc 2
      have hlog : Real.log (c ^ 2) ≤ Real.log (Real.sin xw ^ 2 + Real.sinh yw ^ 2) :=
        Real.log_le_log hc2 hB_ge
      have he : Real.log (c ^ 2) = 2 * Real.log c := by rw [Real.log_pow]; norm_num
      linarith [hlog, he]
    have h4 := core_up M c s u hM hc hs hu hM2c hcs10
    linarith
  have hYX : (1 / 2) * Real.log (Real.sin xw ^ 2 + Real.sinh yw ^ 2)
      - (1 / 2) * Real.log (Real.sin xv ^ 2 + Real.sinh yv ^ 2)
      ≤ 10 + Real.log (1 + u / s) := by
    have h4 : (1 / 2) * Real.log (Real.sin xw ^ 2 + Real.sinh yw ^ 2)
        ≤ (1 / 2) * Real.log ((2*s) ^ 2 + vv ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hBpos hB_le) (by norm_num)
    have h5 : Real.log c ≤ (1 / 2) * Real.log (Real.sin xv ^ 2 + Real.sinh yv ^ 2) := by
      have hc2 : 0 < c ^ 2 := pow_pos hc 2
      have hlog : Real.log (c ^ 2) ≤ Real.log (Real.sin xv ^ 2 + Real.sinh yv ^ 2) :=
        Real.log_le_log hc2 hA_ge
      have he : Real.log (c ^ 2) = 2 * Real.log c := by rw [Real.log_pow]; norm_num
      linarith [hlog, he]
    have h6 := core_low c (2*s) vv hc (by linarith [hs]) hv0 hbound
    have h7 : 0 ≤ Real.log (1 + u / s) :=
      Real.log_nonneg (by have : 0 ≤ u/s := div_nonneg hu (le_of_lt hs); linarith)
    linarith
  exact abs_sub_le_iff.mpr ⟨hXY, hYX⟩

end Work.PARIMPL2.Direct
