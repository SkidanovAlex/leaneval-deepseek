import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.ecalPt_im_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Componentwise bounds for the Écalle point at an almost purely imaginary parameter

For the Écalle point map `ζ(u) = ecalPt (iλ) u = iλ·coth(iλ u)` of
`Submission/Work/Implosion/Ecalle.lean`, with `λ > 0`, we bound the real and the
imaginary part of `ζ(u)` by `λ / sin(λ·Re u)`.

Writing `p = sin θ` with `θ = λ·Re u`, `s = sinh η`, `c = cosh η` with
`η = λ·Im u`, the explicit formulas (`inbound_ecalPt_re`, `ecalPt_im_eq`) read

  `Re ζ(u) = λ·p·cos θ / E`,   `Im ζ(u) = −λ·s·c / E`,
  `E = p² + s² = ‖sin(λu)‖²`.

* For the real part, `|cos θ| ≤ 1` gives `λ·p·|cos θ|/E ≤ λ·p/E ≤ λ/p`, because
  `p² ≤ E`.
* For the imaginary part, the hypothesis `c = cosh η ≤ 2` together with `|s| ≤
  cosh η = c`-free AM–GM `2·p·|s| ≤ p² + s²` gives
  `λ·|s|·c/E ≤ 2λ·p·|s|/E ≤ λ/p`.

The bound on the real part is the estimate needed to keep `ζ` in a small disc;
the bound on the imaginary part controls the height drift.
-/

namespace Work.PARIMPL2.Direct

open Complex

theorem ecalPtAbsReImLe (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (hsin : 0 < Real.sin (lam * u.re)) (hcosh : Real.cosh (lam * u.im) ≤ 2) :
    |(Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re| ≤ lam / Real.sin (lam * u.re) ∧
      |(Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im| ≤ lam / Real.sin (lam * u.re) := by
  have hcosh_pos : 0 < Real.cosh (lam * u.im) := Real.cosh_pos _
  -- the parameter is not a puncture: `sin (λu) ≠ 0`, hence `ecalE (iλ) u ≠ 1`
  have hsinC_ne : Complex.sin ((lam : ℂ) * u) ≠ 0 := by
    intro h
    have hre0 : (Complex.sin ((lam : ℂ) * u)).re = 0 := by rw [h]; simp
    rw [inbound_sin_re] at hre0
    rcases mul_eq_zero.mp hre0 with h1 | h1
    · linarith [hsin, h1]
    · exact absurd h1 hcosh_pos.ne'
  have hsinh_ne : Complex.sinh (((lam : ℂ) * Complex.I) * u) ≠ 0 := by
    intro h
    apply hsinC_ne
    have h2 : ((lam : ℂ) * Complex.I) * u = ((lam : ℂ) * u) * Complex.I := by ring
    rw [h2, Complex.sinh_mul_I] at h
    rcases mul_eq_zero.mp h with h3 | h3
    · exact h3
    · exact absurd h3 Complex.I_ne_zero
  have hE_ne : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1 := by
    intro h
    have h1 := inbound_ecalE_sub_one ((lam : ℂ) * Complex.I) u
    rw [h, sub_self] at h1
    have h3 : Complex.sinh (((lam : ℂ) * Complex.I) * u) = 0 := by
      rcases mul_eq_zero.mp h1.symm with h4 | h4
      · rcases mul_eq_zero.mp h4 with h5 | h5
        · norm_num at h5
        · exact h5
      · exact absurd h4 (Complex.exp_ne_zero _)
    exact hsinh_ne h3
  -- abbreviations for the computation
  set p : ℝ := Real.sin (lam * u.re) with hp
  set s : ℝ := Real.sinh (lam * u.im) with hs
  set q : ℝ := |s| with hq
  set c : ℝ := Real.cosh (lam * u.im) with hc
  set E : ℝ := p ^ 2 + q ^ 2 with hE
  have hp_pos : 0 < p := by rw [hp]; exact hsin
  have hq_nonneg : 0 ≤ q := by rw [hq]; exact abs_nonneg s
  have hc_pos : 0 < c := by rw [hc]; exact hcosh_pos
  have hc_le : c ≤ 2 := by rw [hc]; exact hcosh
  have hEpos : 0 < E := by rw [hE]; nlinarith [sq_pos_of_pos hp_pos, sq_nonneg q]
  have hE' : E = Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
    rw [hE, hp, hq, hs, sq_abs]
  -- closed forms for the two components
  have hre : (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re
      = lam * (p * Real.cos (lam * u.re)) / E := by
    rw [inbound_ecalPt_re lam hlam u hE_ne, inbound_sq_abs_sin lam u, ← hE', ← hp]
  have him : (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im
      = (-(lam * s * c)) / E := by
    rw [ecalPt_im_eq lam u E hE', ← hs, ← hc]
  -- real part: `|cos θ| ≤ 1` and `p² ≤ E`
  have hb_re : |lam * (p * Real.cos (lam * u.re)) / E| ≤ lam / p := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos hp_pos, abs_of_pos hEpos]
    have hcos : |Real.cos (lam * u.re)| ≤ 1 := Real.abs_cos_le_one _
    have h1 : p * |Real.cos (lam * u.re)| ≤ p := by
      simpa using mul_le_of_le_one_right hp_pos.le hcos
    have h2 : p * |Real.cos (lam * u.re)| ≤ E / p := by
      rw [le_div_iff₀ hp_pos]
      have h3 : (p * |Real.cos (lam * u.re)|) * p ≤ p * p :=
        mul_le_mul_of_nonneg_right h1 hp_pos.le
      have h4 : p * p ≤ E := by rw [hE]; nlinarith [sq_nonneg q]
      linarith [h3, h4]
    rw [div_le_iff₀ hEpos]
    have h5 : lam * (p * |Real.cos (lam * u.re)|) ≤ lam * (E / p) :=
      mul_le_mul_of_nonneg_left h2 hlam.le
    have h6 : lam * (E / p) = lam / p * E := by
      rw [div_mul_eq_mul_div, ← mul_div_assoc]
    linarith [h5, h6]
  -- imaginary part: `|sinh η|·cosh η ≤ 2|sinh η|` and AM–GM `2 p |s| ≤ p² + s²`
  have hb_im_abs : |(-(lam * s * c)) / E| = lam * (q * c) / E := by
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos hc_pos,
      abs_of_pos hEpos, ← hq]
    ring
  have hb_im : |(-(lam * s * c)) / E| ≤ lam / p := by
    rw [hb_im_abs, div_le_iff₀ hEpos]
    have h1 : q * c ≤ 2 * q := by
      have := mul_le_mul_of_nonneg_left hc_le hq_nonneg
      linarith
    have h2 : p * (q * c) ≤ p * (2 * q) := mul_le_mul_of_nonneg_left h1 hp_pos.le
    have h3 : 2 * (p * q) ≤ E := by rw [hE]; nlinarith [sq_nonneg (p - q)]
    have h4 : p * q * c ≤ E := by nlinarith [h2, h3]
    have h5 : q * c ≤ E / p := by
      rw [le_div_iff₀ hp_pos]
      have h6 : (q * c) * p = p * q * c := by ring
      rw [h6]; exact h4
    have h7 : lam * (q * c) ≤ lam * (E / p) := mul_le_mul_of_nonneg_left h5 hlam.le
    have h8 : lam * (E / p) = lam / p * E := by
      rw [div_mul_eq_mul_div, ← mul_div_assoc]
    rw [← h8]
    exact h7
  have hb1 : |(Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re|
      ≤ lam / Real.sin (lam * u.re) := by
    rw [hre, ← hp]; exact hb_re
  have hb2 : |(Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im|
      ≤ lam / Real.sin (lam * u.re) := by
    rw [him, ← hp]; exact hb_im
  exact ⟨hb1, hb2⟩

end Work.PARIMPL2.Direct
