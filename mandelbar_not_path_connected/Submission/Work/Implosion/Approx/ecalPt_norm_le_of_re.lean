import Mathlib
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-! ## Elementary norm formulae for `cos` and `sin` on a vertical line

For `w = x + iy` the addition theorems give
`‖cos w‖ ^ 2 = cos x ^ 2 + sinh y ^ 2` and `‖sin w‖ ^ 2 = sin x ^ 2 + sinh y ^ 2`.
These are the only complex-analytic inputs of the estimate below. -/

private lemma normSq_cos_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.cos_sq_add_sin_sq x, Real.cosh_sq_sub_sinh_sq y]

private lemma normSq_sin_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.cos_sq_add_sin_sq x, Real.cosh_sq_sub_sinh_sq y]

private lemma normSq_cos_eq (w : ℂ) :
    Complex.normSq (Complex.cos w) = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  conv_lhs => rw [← Complex.re_add_im w]
  exact normSq_cos_add_mul_I w.re w.im

private lemma normSq_sin_eq (w : ℂ) :
    Complex.normSq (Complex.sin w) = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  conv_lhs => rw [← Complex.re_add_im w]
  exact normSq_sin_add_mul_I w.re w.im

private lemma sin_ne_zero_of_re (w : ℂ) (h1 : 0 < w.re) (h2 : w.re < Real.pi) :
    Complex.sin w ≠ 0 := by
  intro h
  have hsin := normSq_sin_eq w
  rw [h] at hsin
  simp only [Complex.normSq_zero] at hsin
  have hs : 0 < Real.sin w.re := Real.sin_pos_of_pos_of_lt_pi h1 h2
  nlinarith [sq_pos_of_pos hs, sq_nonneg (Real.sinh w.im)]

/-- **The key estimate.**  On the vertical line `Re w ∈ (0, π)`,

`‖cot w‖ ≤ 1 / sin (Re w)`.

The bound is sharp at `Im w = 0` and is the only place where the two ends `0`, `π`
of the strip enter. -/
private lemma norm_cot_le (w : ℂ) (h1 : 0 < w.re) (h2 : w.re < Real.pi) :
    ‖Complex.cot w‖ ≤ 1 / Real.sin w.re := by
  have hcos := normSq_cos_eq w
  have hsin := normSq_sin_eq w
  have hs : 0 < Real.sin w.re := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hsinne : Complex.sin w ≠ 0 := sin_ne_zero_of_re w h1 h2
  have hsinpos : 0 < ‖Complex.sin w‖ := norm_pos_iff.mpr hsinne
  rw [Complex.cot_eq_cos_div_sin, norm_div, div_le_div_iff₀ hsinpos hs, one_mul]
  have key : (‖Complex.cos w‖ * Real.sin w.re) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, hcos, hsin]
    nlinarith [Real.sin_sq w.re, sq_nonneg (Real.sin w.re), sq_nonneg (Real.sinh w.im)]
  calc ‖Complex.cos w‖ * Real.sin w.re
      ≤ Real.sqrt (‖Complex.sin w‖ ^ 2) :=
        (Real.le_sqrt (mul_nonneg (norm_nonneg _) hs.le) (sq_nonneg _)).mpr key
    _ = ‖Complex.sin w‖ := Real.sqrt_sq (norm_nonneg _)

/-- Jordan's inequality on the whole interval: for `0 < t < π`,
`(2/π) * min t (π - t) ≤ sin t`.  Both halves come from `Real.mul_le_sin`. -/
private lemma two_div_pi_mul_min_le_sin (t : ℝ) (h1 : 0 < t) (h2 : t < Real.pi) :
    (2 / Real.pi) * min t (Real.pi - t) ≤ Real.sin t := by
  rcases lt_or_ge t (Real.pi / 2) with hlt | hge
  · rw [min_eq_left (by linarith)]
    exact Real.mul_le_sin h1.le (le_of_lt hlt)
  · have h3 : Real.pi - t ≤ Real.pi / 2 := by linarith
    have h4 : 0 ≤ Real.pi - t := by linarith
    rw [min_eq_right (by linarith), ← Real.sin_pi_sub]
    exact Real.mul_le_sin h4 h3

/-- For `a = i·λ` the Écalle point map is `λ·cot(λu)`: this is `ζ(u) = a·coth(a u)`
(`ecallePt_eq_coth`) together with `coth (i w) = -i cot w`. -/
private lemma ecalPt_eq_lam_mul_cot (lam : ℝ) (u : ℂ) (hs : ecalE ((lam : ℂ) * I) u ≠ 1)
    (hsin : Complex.sin ((lam : ℂ) * u) ≠ 0) :
    ecalPt ((lam : ℂ) * I) u = (lam : ℂ) * Complex.cot ((lam : ℂ) * u) := by
  rw [Ecalle.ecallePt_eq_coth _ _ hs, coth,
    show ((lam : ℂ) * I) * u = ((lam : ℂ) * u) * I by ring,
    Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cot_eq_cos_div_sin]
  field_simp
  try ring

theorem ecalPt_norm_le_of_re (lam : ℝ) (u : ℂ) (hl : 0 < lam)
    (h1 : 0 < u.re) (h2 : u.re < Real.pi / lam) :
    ‖ecalPt ((lam:ℂ) * I) u‖ ≤ 10 * (lam + 1 / min u.re (Real.pi / lam - u.re)) := by
  set d := min u.re (Real.pi / lam - u.re) with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact lt_min h1 (by rw [sub_pos]; exact h2)
  set w : ℂ := (lam : ℂ) * u with hw
  have hwre : w.re = lam * u.re := by rw [hw]; simp [Complex.mul_re]
  have hwr1 : 0 < w.re := by rw [hwre]; exact mul_pos hl h1
  have hwr2 : w.re < Real.pi := by
    rw [hwre]
    have hpi : lam * (Real.pi / lam) = Real.pi := by field_simp
    calc lam * u.re < lam * (Real.pi / lam) := mul_lt_mul_of_pos_left h2 hl
      _ = Real.pi := hpi
  have hmin : lam * d = min (lam * u.re) (Real.pi - lam * u.re) := by
    rw [hd, mul_min_of_nonneg u.re (Real.pi / lam - u.re) hl.le]
    congr 1
    field_simp
  have hsinbd : (2 / Real.pi) * (lam * d) ≤ Real.sin w.re := by
    have h := two_div_pi_mul_min_le_sin (lam * u.re) (mul_pos hl h1) (by rw [← hwre]; exact hwr2)
    rw [hwre, hmin]
    exact h
  rcases eq_or_ne (ecalE ((lam : ℂ) * I) u) 1 with hs | hs
  · have hz : ecalPt ((lam : ℂ) * I) u = 0 := by simp [ecalPt, hs]
    rw [hz, norm_zero]
    have h1d : 0 < 1 / d := one_div_pos.mpr hdpos
    linarith
  · have hsinne_w : Complex.sin w ≠ 0 := sin_ne_zero_of_re w hwr1 hwr2
    have hpt : ecalPt ((lam : ℂ) * I) u = (lam : ℂ) * Complex.cot w := by
      rw [hw]
      exact ecalPt_eq_lam_mul_cot lam u hs hsinne_w
    have hcot : ‖Complex.cot w‖ ≤ 1 / Real.sin w.re := norm_cot_le w hwr1 hwr2
    have hnormlam : ‖((lam : ℝ) : ℂ)‖ = lam := by
      have h : ‖((lam : ℝ) : ℂ)‖ = |lam| := RCLike.norm_ofReal lam
      rw [h, abs_of_pos hl]
    calc ‖ecalPt ((lam : ℂ) * I) u‖ = lam * ‖Complex.cot w‖ := by
          rw [hpt, norm_mul, hnormlam]
      _ ≤ lam * (1 / Real.sin w.re) := mul_le_mul_of_nonneg_left hcot hl.le
      _ ≤ Real.pi / (2 * d) := by
          have hpospos : 0 < (2 / Real.pi) * (lam * d) := by
            have h2pi : 0 < 2 / Real.pi := by positivity
            exact mul_pos h2pi (mul_pos hl hdpos)
          have hrec : 1 / Real.sin w.re ≤ 1 / ((2 / Real.pi) * (lam * d)) :=
            one_div_le_one_div_of_le hpospos hsinbd
          calc lam * (1 / Real.sin w.re)
              ≤ lam * (1 / ((2 / Real.pi) * (lam * d))) :=
                mul_le_mul_of_nonneg_left hrec hl.le
            _ = Real.pi / (2 * d) := by
                field_simp
                try ring
      _ ≤ 10 * (lam + 1 / d) := by
          have hA : Real.pi / (2 * d) ≤ 10 / d := by
            rw [div_le_div_iff₀ (by positivity) hdpos]
            nlinarith [Real.pi_lt_four, hdpos]
          have hB : 10 / d ≤ 10 * (lam + 1 / d) := by
            have hlam10 : 0 < 10 * lam := by linarith
            have hexp : 10 * (lam + 1 / d) = 10 * lam + 10 / d := by ring
            rw [hexp]
            linarith
          linarith

end Work.Implosion.Approx
