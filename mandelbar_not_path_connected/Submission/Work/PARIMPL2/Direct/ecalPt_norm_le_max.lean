import Mathlib
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A norm bound for the Écalle point map at an almost purely imaginary parameter

For `a = (lam : ℂ) * I` with `lam > 0` and `u` in the half strip
`0 < u.re < π/(2 lam)`, the Écalle point map
`ecalPt a u = a·(e^{2au}+1)/(e^{2au}−1) = a·coth(a u)` satisfies

  `‖ecalPt a u‖ ≤ max (1 / u.re) lam`.

Writing `t = lam * u.re` and `s = lam * u.im`, the complex hyperbolic cotangent
identity `‖coth (a u)‖^2 = (cos²t + sinh²s)/(sin²t + sinh²s)` reduces the claim to
`min t 1 · sqrt((cos²t + sinh²s)/(sin²t + sinh²s)) ≤ 1`, which splits into
`t² cos²t ≤ sin²t` (for `t ≤ 1`, i.e. `t ≤ tan t`) and `cos²t ≤ sin²t`
(for `t ≥ 1 > π/4`).
-/

namespace Work.PARIMPL2.Direct

namespace EcalNorm

open Complex

/-! ## Real and imaginary parts of `cosh` and `sinh` on `ℂ` -/

theorem cosh_re (z : ℂ) : (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.cosh_add, ← Complex.ofReal_cosh z.re, ← Complex.ofReal_sinh z.re,
      Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos z.im, ← Complex.ofReal_sin z.im]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero, zero_sub]
  ring

theorem cosh_im (z : ℂ) : (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.cosh_add, ← Complex.ofReal_cosh z.re, ← Complex.ofReal_sinh z.re,
      Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos z.im, ← Complex.ofReal_sin z.im]
  simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
  ring

theorem sinh_re (z : ℂ) : (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.sinh_add, ← Complex.ofReal_cosh z.re, ← Complex.ofReal_sinh z.re,
      Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos z.im, ← Complex.ofReal_sin z.im]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero, zero_sub]
  ring

theorem sinh_im (z : ℂ) : (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.sinh_add, ← Complex.ofReal_cosh z.re, ← Complex.ofReal_sinh z.re,
      Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos z.im, ← Complex.ofReal_sin z.im]
  simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
  ring

/-- `‖cosh z‖² = cos²(Im z) + sinh²(Re z)`. -/
theorem norm_sq_cosh (z : ℂ) :
    ‖Complex.cosh z‖ ^ 2 = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, cosh_re z, cosh_im z]
  nlinarith [Real.cosh_sq z.re, Real.sin_sq_add_cos_sq z.im]

/-- `‖sinh z‖² = sin²(Im z) + sinh²(Re z)`. -/
theorem norm_sq_sinh (z : ℂ) :
    ‖Complex.sinh z‖ ^ 2 = Real.sin z.im ^ 2 + Real.sinh z.re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sinh_re z, sinh_im z]
  nlinarith [Real.cosh_sq z.re, Real.sin_sq_add_cos_sq z.im]

/-! ## Elementary trigonometric inequalities on `(0, π/2)` -/

/-- For `1 ≤ t < π/2` one has `cos² t ≤ sin² t`. -/
theorem sq_cos_le_sq_sin {t : ℝ} (ht : 1 ≤ t) (ht2 : t < Real.pi / 2) :
    Real.cos t ^ 2 ≤ Real.sin t ^ 2 := by
  have h1 : Real.pi / 2 ≤ 2 * t := by linarith [Real.pi_lt_four]
  have h2 : 2 * t ≤ Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
  have hc : Real.cos (2 * t) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
  have hcm : Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 := Real.cos_two_mul t
  have hs : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  nlinarith [hc, hcm, hs]

/-- For `0 ≤ t < π/2` one has `t² cos² t ≤ sin² t`. -/
theorem sq_mul_sq_cos_le_sq_sin {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < Real.pi / 2) :
    t ^ 2 * Real.cos t ^ 2 ≤ Real.sin t ^ 2 := by
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht2⟩
  have htan : t ≤ Real.tan t := Real.le_tan ht0 ht2
  have hmul : t * Real.cos t ≤ Real.sin t := by
    have := mul_le_mul_of_nonneg_right htan hcos.le
    rwa [Real.tan_mul_cos hcos.ne'] at this
  have h0 : 0 ≤ t * Real.cos t := mul_nonneg ht0 hcos.le
  have hsq := pow_le_pow_left₀ h0 hmul 2
  rwa [mul_pow] at hsq

end EcalNorm

theorem ecalPt_norm_le_max (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h1 : 0 < u.re) (h2 : u.re < Real.pi / (2 * lam)) :
    ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ max (1 / u.re) lam := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set w : ℂ := a * u with hw
  set t : ℝ := lam * u.re with ht
  set s : ℝ := lam * u.im with hs
  have ht_pos : 0 < t := by rw [ht]; exact mul_pos hlam h1
  have ht_lt : t < Real.pi / 2 := by
    have hpi : lam * (Real.pi / (2 * lam)) = Real.pi / 2 := by
      field_simp
    calc lam * u.re < lam * (Real.pi / (2 * lam)) := mul_lt_mul_of_pos_left h2 hlam
      _ = Real.pi / 2 := hpi
  have ht_lt_pi : t < Real.pi := by linarith [Real.pi_pos]
  have hw_im : w.im = t := by
    rw [hw, ha, ht]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    ring
  have hw_re : w.re = -s := by
    rw [hw, ha, hs]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    ring
  have hcosh : ‖Complex.cosh w‖ ^ 2 = Real.cos t ^ 2 + Real.sinh s ^ 2 := by
    rw [EcalNorm.norm_sq_cosh, hw_im, hw_re, Real.sinh_neg]
    ring
  have hsinh : ‖Complex.sinh w‖ ^ 2 = Real.sin t ^ 2 + Real.sinh s ^ 2 := by
    rw [EcalNorm.norm_sq_sinh, hw_im, hw_re, Real.sinh_neg]
    ring
  have hden_pos : 0 < Real.sin t ^ 2 + Real.sinh s ^ 2 := by
    have hsp := Real.sin_pos_of_pos_of_lt_pi ht_pos ht_lt_pi
    nlinarith [sq_pos_of_pos hsp, sq_nonneg (Real.sinh s)]
  have hE : Work.Implosion.ecalE a u ≠ 1 := by
    intro h
    have him : (Work.Implosion.ecalE a u).im = 0 := by rw [h]; simp
    rw [Work.Implosion.ecalE, Complex.exp_im] at him
    have h2au : (2 * a * u).im = 2 * t := by
      have h2w : 2 * a * u = 2 * w := by rw [hw]; ring
      rw [h2w]
      simp only [Complex.mul_im, hw_im]
      norm_num
    rw [h2au] at him
    have hsin2 : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rcases mul_eq_zero.mp him with h' | h'
    · exact Real.exp_ne_zero _ h'
    · exact hsin2.ne' h'
  have hnorm : ‖Work.Implosion.ecalPt a u‖ =
      lam * (‖Complex.cosh w‖ / ‖Complex.sinh w‖) := by
    rw [Work.Implosion.Ecalle.ecallePt_eq_coth a u hE, Work.Implosion.coth, ← hw]
    rw [Complex.norm_mul, Complex.norm_div]
    have hna : ‖a‖ = lam := by
      rw [ha, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      exact abs_of_pos hlam
    rw [hna]
  have hX2 : ‖Work.Implosion.ecalPt a u‖ ^ 2 =
      lam ^ 2 * ((Real.cos t ^ 2 + Real.sinh s ^ 2) /
        (Real.sin t ^ 2 + Real.sinh s ^ 2)) := by
    rw [hnorm, mul_pow, div_pow, hcosh, hsinh]
  by_cases hcase : 1 ≤ t
  · have hcs : Real.cos t ^ 2 ≤ Real.sin t ^ 2 := EcalNorm.sq_cos_le_sq_sin hcase ht_lt
    have hle : ‖Work.Implosion.ecalPt a u‖ ≤ lam := by
      have hsq : ‖Work.Implosion.ecalPt a u‖ ^ 2 ≤ lam ^ 2 := by
        rw [hX2]
        have hstep : (Real.cos t ^ 2 + Real.sinh s ^ 2) /
            (Real.sin t ^ 2 + Real.sinh s ^ 2) ≤ 1 :=
          (div_le_one hden_pos).mpr (by linarith)
        calc lam ^ 2 * ((Real.cos t ^ 2 + Real.sinh s ^ 2) /
              (Real.sin t ^ 2 + Real.sinh s ^ 2))
            ≤ lam ^ 2 * 1 := mul_le_mul_of_nonneg_left hstep (sq_nonneg lam)
          _ = lam ^ 2 := by ring
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hlam.le] at this
    exact le_max_of_le_right hle
  · simp only [not_le] at hcase
    have hle : ‖Work.Implosion.ecalPt a u‖ ≤ 1 / u.re := by
      have h1u : 1 / u.re = lam / t := by
        rw [ht]; field_simp
      have hB2 : (1 / u.re) ^ 2 = lam ^ 2 * (1 / t ^ 2) := by
        rw [h1u, div_pow]; ring
      have ht2pos : 0 < t ^ 2 := pow_pos ht_pos 2
      have hstep : (Real.cos t ^ 2 + Real.sinh s ^ 2) /
          (Real.sin t ^ 2 + Real.sinh s ^ 2) ≤ 1 / t ^ 2 := by
        rw [div_le_iff₀ hden_pos]
        have hrw : (1 / t ^ 2) * (Real.sin t ^ 2 + Real.sinh s ^ 2) =
            (Real.sin t ^ 2 + Real.sinh s ^ 2) / t ^ 2 := by ring
        rw [hrw, le_div_iff₀ ht2pos]
        have h1' : t ^ 2 * Real.cos t ^ 2 ≤ Real.sin t ^ 2 :=
          EcalNorm.sq_mul_sq_cos_le_sq_sin ht_pos.le ht_lt
        have h2' : t ^ 2 * Real.sinh s ^ 2 ≤ Real.sinh s ^ 2 := by
          have ht1 : t ^ 2 ≤ 1 := by nlinarith
          exact mul_le_of_le_one_left (sq_nonneg _) ht1
        nlinarith [h1', h2']
      have hsq : ‖Work.Implosion.ecalPt a u‖ ^ 2 ≤ (1 / u.re) ^ 2 := by
        rw [hX2, hB2]
        calc lam ^ 2 * ((Real.cos t ^ 2 + Real.sinh s ^ 2) /
              (Real.sin t ^ 2 + Real.sinh s ^ 2))
            ≤ lam ^ 2 * (1 / t ^ 2) := mul_le_mul_of_nonneg_left hstep (sq_nonneg lam)
          _ = lam ^ 2 * (1 / t ^ 2) := rfl
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt (one_div_pos.mpr h1))] at this
    exact le_max_of_le_left hle

end Work.PARIMPL2.Direct
