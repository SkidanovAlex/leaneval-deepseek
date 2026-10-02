import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.norm_modelDisp_add_rational_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.PARIMPL2.Direct

open Complex

/-- Tight companion of `norm_modelDisp_add_rational_le`: in the regime `‖ζ‖ ≤ 1/32`,
`‖h ζ‖ ≤ 2` and `lam ≤ 1/32`, the model displacement `Φ` agrees with the rational
expression `h(ζ)/(1+ζ·h(ζ))` (with the sign) up to `9·λ²`, instead of `100·λ²`.

The gain is entirely in the size of the denominator: `‖ζ·h(ζ)‖ ≤ 1/16` gives `‖c‖ ≥ 15/16`
(rather than `1/2`), hence `‖w‖ = ‖a·h(ζ)/c‖ ≤ 32λ/15` instead of `4λ`. -/
theorem norm_modelDisp_add_rational_le_tight (lam : ℝ) (hlam : 0 < lam) (hlam32 : lam ≤ 1 / 32)
    (h : ℂ → ℂ) (u : ℂ)
    (hζ : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 1 / 32)
    (hH : ‖h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u)‖ ≤ 2) :
    ‖Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u
      + h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u)
        / (1 + Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u
            * h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u))‖
      ≤ 9 * lam ^ 2 := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζa
  set H : ℂ := h ζ with hHa
  set c : ℂ := 1 + ζ * H with hc
  set w : ℂ := a * H / c with hw
  have hlne : lam ≠ 0 := ne_of_gt hlam
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hlne) Complex.I_ne_zero
  have hanorm : ‖a‖ = lam := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hlam
  have hζ' : ‖ζ‖ ≤ 1 / 32 := by rw [hζa]; exact hζ
  have hH' : ‖H‖ ≤ 2 := by rw [hHa]; exact hH
  have hζH : ‖ζ * H‖ ≤ 1 / 16 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ (1 / 32) * 2 := mul_le_mul hζ' hH' (norm_nonneg H) (by norm_num)
      _ = 1 / 16 := by norm_num
  have hcd : ‖c - 1‖ ≤ 1 / 16 := by
    have hce : c - 1 = ζ * H := by rw [hc]; ring
    rw [hce]; exact hζH
  have hc_lower : (15 / 16 : ℝ) ≤ ‖c‖ := by
    have h1 : (1 : ℝ) - ‖c‖ ≤ ‖(1 : ℂ) - c‖ := by
      have := norm_sub_norm_le (1 : ℂ) c
      rwa [norm_one] at this
    rw [norm_sub_rev] at h1
    linarith
  have hre_c : 0 < c.re := by
    have h2 : c.re = 1 + (ζ * H).re := by rw [hc]; simp
    have h5 : -(1 / 16 : ℝ) ≤ (ζ * H).re := by
      have h6 := (abs_le.mp (Complex.abs_re_le_norm (ζ * H))).1
      linarith [h6, hζH]
    rw [h2]; linarith
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at hre_c; simp at hre_c
  have hw_le : ‖w‖ ≤ 32 * lam / 15 := by
    have hwn : ‖w‖ = lam * ‖H‖ * ‖c‖⁻¹ := by
      rw [hw, norm_div, norm_mul, hanorm, div_eq_mul_inv]
    rw [hwn]
    have hcinv : ‖c‖⁻¹ ≤ (15 / 16 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0 : ℝ) < ‖c‖) (by norm_num : (0 : ℝ) < 15 / 16)]
      exact hc_lower
    have hHsq : ‖H‖ ^ 2 ≤ 4 := by nlinarith [hH', norm_nonneg H]
    have hstep : lam * ‖H‖ ≤ lam * 2 := mul_le_mul_of_nonneg_left hH' (le_of_lt hlam)
    calc lam * ‖H‖ * ‖c‖⁻¹ ≤ lam * 2 * (15 / 16 : ℝ)⁻¹ :=
          mul_le_mul hstep hcinv (by positivity) (by positivity)
      _ = 32 * lam / 15 := by
          rw [show ((15 : ℝ) / 16)⁻¹ = 16 / 15 by norm_num]; ring
  have hw_small : ‖w‖ ≤ 3 / 5 := by
    have h1 : 32 * lam / 15 ≤ 3 / 5 := by linarith [hlam32]
    linarith
  have hw_re_pos : 0 < (1 - w).re := by
    have h1 : w.re ≤ ‖w‖ := (abs_le.mp (Complex.abs_re_le_norm w)).2
    rw [Complex.sub_re, Complex.one_re]
    linarith [hw_small, h1]
  have hw_re_pos2 : 0 < (1 + w).re := by
    have h1 : -(‖w‖) ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
    rw [Complex.add_re, Complex.one_re]
    linarith [hw_small, h1]
  have hw1 : 1 - w ≠ 0 := by intro h0; rw [h0] at hw_re_pos; simp at hw_re_pos
  have hw2 : 1 + w ≠ 0 := by intro h0; rw [h0] at hw_re_pos2; simp at hw_re_pos2
  have ha1 : c.arg + (1 - w).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    Work.Implosion.Approx.arg_add_mem_Ioc_of_re_pos hre_c hw_re_pos
  have ha2 : c.arg + (1 + w).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    Work.Implosion.Approx.arg_add_mem_Ioc_of_re_pos hre_c hw_re_pos2
  have hid : 2 * a * (Work.Implosion.modelDisp a h u + H * c⁻¹)
      = Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w :=
    Work.Implosion.Approx.two_a_mul_modelDisp_add_inv a h u ζ H c w ha0 hζa hHa hc hw
      hc0 hw1 hw2 ha1 ha2
  have h2a : (2 : ℂ) * a ≠ 0 := mul_ne_zero (by norm_num) ha0
  have hsplit : Work.Implosion.modelDisp a h u + H * c⁻¹
      = (Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w) / (2 * a) := by
    rw [eq_div_iff h2a, mul_comm]
    exact hid
  have hlogRem_neg : ‖Work.Implosion.Approx.logRem (-w)‖ ≤ 5 * ‖w‖ ^ 3 / 6 := by
    have hh := Work.Implosion.Approx.norm_logRem_le_three_fifths (-w)
      (by rw [norm_neg]; exact hw_small)
    simpa [norm_neg] using hh
  have hlogRem_pos : ‖Work.Implosion.Approx.logRem w‖ ≤ 5 * ‖w‖ ^ 3 / 6 :=
    Work.Implosion.Approx.norm_logRem_le_three_fifths w hw_small
  have hcorr : ‖Work.Implosion.modelDisp a h u + H * c⁻¹‖ ≤ 5 * ‖w‖ ^ 3 / (6 * lam) := by
    rw [hsplit, norm_div]
    have h2an : ‖(2 : ℂ) * a‖ = 2 * lam := by
      rw [norm_mul, Complex.norm_ofNat, hanorm]
    rw [h2an]
    have hsum : ‖Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w‖
        ≤ 5 * ‖w‖ ^ 3 / 3 := by
      calc ‖Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w‖
          ≤ ‖Work.Implosion.Approx.logRem (-w)‖ + ‖Work.Implosion.Approx.logRem w‖ :=
            norm_sub_le _ _
        _ ≤ 5 * ‖w‖ ^ 3 / 6 + 5 * ‖w‖ ^ 3 / 6 := add_le_add hlogRem_neg hlogRem_pos
        _ = 5 * ‖w‖ ^ 3 / 3 := by ring
    calc ‖Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w‖ / (2 * lam)
        ≤ (5 * ‖w‖ ^ 3 / 3) / (2 * lam) := div_le_div_of_nonneg_right hsum (by linarith)
      _ = 5 * ‖w‖ ^ 3 / (6 * lam) := by ring
  have hfin : 5 * ‖w‖ ^ 3 / (6 * lam) ≤ 9 * lam ^ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * lam)]
    have hw3 : ‖w‖ ^ 3 ≤ (32 * lam / 15) ^ 3 := pow_le_pow_left₀ (norm_nonneg w) hw_le 3
    nlinarith [hw3, hlam]
  have hmain : ‖Work.Implosion.modelDisp a h u + H * c⁻¹‖ ≤ 9 * lam ^ 2 := le_trans hcorr hfin
  simpa only [ha, hζa, hHa, hc, div_eq_mul_inv] using hmain

/-- **The signed real-part bound on the model displacement.**

For the rotated local normal form with `ζ = ecalPt (iλ) u` small (`‖ζ‖ ≤ 4/R`, `R ≥ 128`),
`λR² ≤ 1`, and `h ζ = τ + h₁ζ + O(ζ²)` with `‖h₁‖ ≤ B`, the real part of the displacement
satisfies

  `Re Φ ≤ -1 + 35λ² + (B+8)‖ζ‖ - Re(h(ζ) - τ - h₁ζ) + 35‖ζ‖²`.

Unlike `modelDisp_re_le`, the *signed* quadratic remainder `Re(h(ζ) - τ - h₁ζ)` is kept
exactly; the price is the coarser linear coefficient `B+8` (the `8` absorbs the error
`‖h(ζ)/(1+ζh(ζ)) - h(ζ)‖ ≤ 8‖ζ‖` of the rational expression). -/
theorem modelDisp_re_le_signed (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R)) (hrr : 16 ≤ R * r)
    (u : ℂ) (hzn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re
      ≤ -1 + 35 * lam ^ 2 + (B + 8) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖
        - (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re
        + 35 * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζa
  set H : ℂ := h ζ with hHa
  set c : ℂ := 1 + ζ * H with hc
  set Q : ℂ := H / c with hQ
  set Φ : ℂ := Work.Implosion.modelDisp a h u with hΦ
  set RR : ℂ := H - τ - h1 * ζ with hRR
  have hζn : ‖ζ‖ ≤ 4 / R := by rw [hζa, ha]; exact hzn
  have hζr : ‖ζ‖ < r := by rw [hζa, ha]; exact hzr
  have hζle : ‖ζ‖ ≤ 1 / 32 := by
    have h1 : (4 : ℝ) / R ≤ 1 / 32 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 32)]
      linarith
    linarith [hζn, h1]
  have hH2 : ‖H‖ ≤ 2 := by
    rw [hHa]
    exact hb.2.2.2.1 ζ hζr
  have hlam32 : lam ≤ 1 / 32 := by
    have hR2 : (1024 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
    have h1 : lam * 1024 ≤ lam * R ^ 2 := mul_le_mul_of_nonneg_left hR2 (le_of_lt hlam)
    have h2 : lam * 1024 ≤ 1 := by linarith [hlamR, h1]
    linarith
  have hΦQ : ‖Φ + Q‖ ≤ 9 * lam ^ 2 := by
    have hh := norm_modelDisp_add_rational_le_tight lam hlam hlam32 h u
      (by rw [← ha, ← hζa]; exact hζle)
      (by rw [← ha, ← hζa, ← hHa]; exact hH2)
    simpa only [hΦ, hQ, hc, hHa, hζa, ha] using hh
  have hζH : ‖ζ * H‖ ≤ 1 / 16 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ (1 / 32) * 2 := mul_le_mul hζle hH2 (norm_nonneg H) (by norm_num)
      _ = 1 / 16 := by norm_num
  have hc_lower : (15 / 16 : ℝ) ≤ ‖c‖ := by
    have hcd : ‖c - 1‖ ≤ 1 / 16 := by
      have hce : c - 1 = ζ * H := by rw [hc]; ring
      rw [hce]; exact hζH
    have h1 : (1 : ℝ) - ‖c‖ ≤ ‖(1 : ℂ) - c‖ := by
      have := norm_sub_norm_le (1 : ℂ) c
      rwa [norm_one] at this
    rw [norm_sub_rev] at h1
    linarith
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hc_lower; norm_num at hc_lower
  have hHsub : H - Q = ζ * H ^ 2 / c := by
    have hc1 : c - 1 = ζ * H := by rw [hc]; ring
    rw [hQ, eq_div_iff hc0, sub_mul, div_mul_cancel₀ H hc0]
    rw [show H * c - H = H * (c - 1) by ring, hc1]
    ring
  have hHQ : ‖H - Q‖ ≤ 8 * ‖ζ‖ := by
    rw [hHsub, norm_div, norm_mul, norm_pow]
    have hcinv : (‖c‖)⁻¹ ≤ 16 / 15 := by
      rw [show (16 : ℝ) / 15 = ((15 : ℝ) / 16)⁻¹ by norm_num]
      exact (inv_le_inv₀ (by linarith : (0 : ℝ) < ‖c‖) (by norm_num : (0 : ℝ) < 15 / 16)).mpr
        hc_lower
    have hHsq : ‖H‖ ^ 2 ≤ 4 := by nlinarith [hH2, norm_nonneg H]
    have h1 : ‖ζ‖ * ‖H‖ ^ 2 ≤ ‖ζ‖ * 4 := mul_le_mul_of_nonneg_left hHsq (norm_nonneg ζ)
    calc ‖ζ‖ * ‖H‖ ^ 2 / ‖c‖ = ‖ζ‖ * ‖H‖ ^ 2 * ‖c‖⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ ‖ζ‖ * 4 * (16 / 15) := mul_le_mul h1 hcinv (by positivity) (by positivity)
      _ ≤ 8 * ‖ζ‖ := by nlinarith [norm_nonneg ζ]
  have hΦQ_re : Φ.re = (Φ + Q).re - Q.re := by rw [Complex.add_re]; ring
  have hQ_re : Q.re = H.re - (H - Q).re := by
    have : (H - Q).re = H.re - Q.re := by simp [Complex.sub_re]
    linarith
  have hReΦ : Φ.re ≤ -H.re + ‖Φ + Q‖ + ‖H - Q‖ := by
    have h1 : (Φ + Q).re ≤ ‖Φ + Q‖ := Complex.re_le_norm _
    have h2 : (H - Q).re ≤ ‖H - Q‖ := Complex.re_le_norm _
    rw [hΦQ_re, hQ_re]
    linarith
  have hτre : τ.re = 1 - ‖τ - 1‖ ^ 2 / 2 := by
    have hτn : τ.re ^ 2 + τ.im ^ 2 = 1 := by
      have h1 : ‖τ‖ ^ 2 = 1 := by rw [hb.2.1]; norm_num
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      rw [pow_two, pow_two]
      exact h1
    have h2 : ‖τ - 1‖ ^ 2 = 2 - 2 * τ.re := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
      nlinarith [hτn]
    linarith
  have hτsq : ‖τ - 1‖ ^ 2 / 2 ≤ lam ^ 2 := by
    have hpilam : 0 < Real.pi / lam := div_pos Real.pi_pos hlam
    have hτpi' : ‖τ - 1‖ * (Real.pi / lam) ≤ 1 / (8 * R) := by rw [mul_comm]; exact hτpi
    have h1 : ‖τ - 1‖ ≤ (1 / (8 * R)) / (Real.pi / lam) := (le_div_iff₀ hpilam).mpr hτpi'
    have h2 : (1 / (8 * R)) / (Real.pi / lam) = lam / (8 * Real.pi * R) := by
      field_simp
    have h3 : ‖τ - 1‖ ≤ lam / (8 * Real.pi * R) := by linarith [h1, h2]
    have h4 : ‖τ - 1‖ ^ 2 ≤ (lam / (8 * Real.pi * R)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    have hge : (1 : ℝ) ≤ 2 * (8 * Real.pi * R) ^ 2 := by
      have h1' : (1 : ℝ) ≤ 8 * Real.pi * R := by nlinarith [Real.pi_gt_three, hRpos]
      nlinarith [h1']
    have h5 : (lam / (8 * Real.pi * R)) ^ 2 / 2 ≤ lam ^ 2 := by
      rw [div_pow, div_div]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (8 * Real.pi * R) ^ 2 * 2)]
      nlinarith [hge, sq_nonneg lam]
    linarith [h4, h5]
  have hτbound : -τ.re ≤ -1 + lam ^ 2 := by linarith [hτre, hτsq]
  have hh1ζ : -(h1 * ζ).re ≤ B * ‖ζ‖ := by
    calc -(h1 * ζ).re ≤ ‖h1 * ζ‖ := by
          calc -(h1 * ζ).re ≤ |(h1 * ζ).re| := neg_le_abs _
            _ ≤ ‖h1 * ζ‖ := Complex.abs_re_le_norm _
      _ = ‖h1‖ * ‖ζ‖ := norm_mul _ _
      _ ≤ B * ‖ζ‖ := mul_le_mul_of_nonneg_right hh1 (norm_nonneg ζ)
  have hHdecomp : H = τ + h1 * ζ + RR := by rw [hRR]; ring
  have hReH : -H.re ≤ -1 + lam ^ 2 + B * ‖ζ‖ - RR.re := by
    have hRe : H.re = τ.re + (h1 * ζ).re + RR.re := by
      rw [hHdecomp]; simp [Complex.add_re]
    linarith [hRe, hτbound, hh1ζ]
  have hmain : Φ.re ≤ -1 + 10 * lam ^ 2 + (B + 8) * ‖ζ‖ - RR.re := by
    linarith [hReΦ, hΦQ, hHQ, hReH]
  have hfin : Φ.re ≤ -1 + 35 * lam ^ 2 + (B + 8) * ‖ζ‖ - RR.re + 35 * ‖ζ‖ ^ 2 := by
    nlinarith [hmain, sq_nonneg lam, sq_nonneg ‖ζ‖]
  simpa only [ha, hΦ, hζa, hHa, hRR] using hfin

end Work.PARIMPL2.Direct
